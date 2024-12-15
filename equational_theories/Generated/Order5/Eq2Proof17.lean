import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation35200_implies_Equation2 (G : Type*) [Magma G] (h : Equation35200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35202_implies_Equation2 (G : Type*) [Magma G] (h : Equation35202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35203_implies_Equation2 (G : Type*) [Magma G] (h : Equation35203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35204_implies_Equation2 (G : Type*) [Magma G] (h : Equation35204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35205_implies_Equation2 (G : Type*) [Magma G] (h : Equation35205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35208_implies_Equation2 (G : Type*) [Magma G] (h : Equation35208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq73 eq22


@[equational_result]
theorem Equation35209_implies_Equation2 (G : Type*) [Magma G] (h : Equation35209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq9 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation35211_implies_Equation2 (G : Type*) [Magma G] (h : Equation35211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35212_implies_Equation2 (G : Type*) [Magma G] (h : Equation35212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35213_implies_Equation2 (G : Type*) [Magma G] (h : Equation35213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35215_implies_Equation2 (G : Type*) [Magma G] (h : Equation35215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35216_implies_Equation2 (G : Type*) [Magma G] (h : Equation35216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35217_implies_Equation2 (G : Type*) [Magma G] (h : Equation35217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35219_implies_Equation2 (G : Type*) [Magma G] (h : Equation35219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35220_implies_Equation2 (G : Type*) [Magma G] (h : Equation35220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35221_implies_Equation2 (G : Type*) [Magma G] (h : Equation35221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35222_implies_Equation2 (G : Type*) [Magma G] (h : Equation35222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35224_implies_Equation2 (G : Type*) [Magma G] (h : Equation35224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq43 eq19


@[equational_result]
theorem Equation35225_implies_Equation2 (G : Type*) [Magma G] (h : Equation35225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X2 ◇ X4) ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X5 := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = X3 := superpose eq7 eq9
  have eq23 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq14 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ (X2 ◇ (X3 ◇ X4))) = X5 := superpose eq23 eq13
  have eq29 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X2) = X5 := superpose eq23 eq24
  have eq30 (X1 X2 X5 : G) : (X1 ◇ X2) = X5 := superpose eq23 eq29
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation35226_implies_Equation2 (G : Type*) [Magma G] (h : Equation35226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X0))) ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq9
  have eq21 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X0) ◇ X4) = X5 := superpose eq12 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq53 eq31


@[equational_result]
theorem Equation35227_implies_Equation2 (G : Type*) [Magma G] (h : Equation35227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation35229_implies_Equation2 (G : Type*) [Magma G] (h : Equation35229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35230_implies_Equation2 (G : Type*) [Magma G] (h : Equation35230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35231_implies_Equation2 (G : Type*) [Magma G] (h : Equation35231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35232_implies_Equation2 (G : Type*) [Magma G] (h : Equation35232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35234_implies_Equation2 (G : Type*) [Magma G] (h : Equation35234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35235_implies_Equation2 (G : Type*) [Magma G] (h : Equation35235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35236_implies_Equation2 (G : Type*) [Magma G] (h : Equation35236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35237_implies_Equation2 (G : Type*) [Magma G] (h : Equation35237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35239_implies_Equation2 (G : Type*) [Magma G] (h : Equation35239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35240_implies_Equation2 (G : Type*) [Magma G] (h : Equation35240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35241_implies_Equation2 (G : Type*) [Magma G] (h : Equation35241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35242_implies_Equation2 (G : Type*) [Magma G] (h : Equation35242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35244_implies_Equation2 (G : Type*) [Magma G] (h : Equation35244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35245_implies_Equation2 (G : Type*) [Magma G] (h : Equation35245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35246_implies_Equation2 (G : Type*) [Magma G] (h : Equation35246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35247_implies_Equation2 (G : Type*) [Magma G] (h : Equation35247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35248_implies_Equation2 (G : Type*) [Magma G] (h : Equation35248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35250_implies_Equation2 (G : Type*) [Magma G] (h : Equation35250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq10
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq7
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq25 eq12
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq25 eq26
  have eq34 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq25 eq33
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation35251_implies_Equation2 (G : Type*) [Magma G] (h : Equation35251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq48 eq18


@[equational_result]
theorem Equation35252_implies_Equation2 (G : Type*) [Magma G] (h : Equation35252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation35253_implies_Equation2 (G : Type*) [Magma G] (h : Equation35253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35255_implies_Equation2 (G : Type*) [Magma G] (h : Equation35255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq70 eq19


@[equational_result]
theorem Equation35256_implies_Equation2 (G : Type*) [Magma G] (h : Equation35256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq72 eq19


@[equational_result]
theorem Equation35257_implies_Equation2 (G : Type*) [Magma G] (h : Equation35257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq47 eq13


@[equational_result]
theorem Equation35258_implies_Equation2 (G : Type*) [Magma G] (h : Equation35258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation35260_implies_Equation2 (G : Type*) [Magma G] (h : Equation35260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq78 eq22


@[equational_result]
theorem Equation35261_implies_Equation2 (G : Type*) [Magma G] (h : Equation35261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) = X4 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation35262_implies_Equation2 (G : Type*) [Magma G] (h : Equation35262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X3)) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq122 eq41


@[equational_result]
theorem Equation35263_implies_Equation2 (G : Type*) [Magma G] (h : Equation35263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35265_implies_Equation2 (G : Type*) [Magma G] (h : Equation35265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq47 eq17


@[equational_result]
theorem Equation35266_implies_Equation2 (G : Type*) [Magma G] (h : Equation35266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation35267_implies_Equation2 (G : Type*) [Magma G] (h : Equation35267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35268_implies_Equation2 (G : Type*) [Magma G] (h : Equation35268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35270_implies_Equation2 (G : Type*) [Magma G] (h : Equation35270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X7 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X7)) ◇ X1) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation35271_implies_Equation2 (G : Type*) [Magma G] (h : Equation35271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X0) ◇ X6)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation35272_implies_Equation2 (G : Type*) [Magma G] (h : Equation35272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35273_implies_Equation2 (G : Type*) [Magma G] (h : Equation35273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35274_implies_Equation2 (G : Type*) [Magma G] (h : Equation35274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X8 : G) : (X0 ◇ X8) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35276_implies_Equation2 (G : Type*) [Magma G] (h : Equation35276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X1) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq16 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation35277_implies_Equation2 (G : Type*) [Magma G] (h : Equation35277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0))) ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X3 ◇ X1) ◇ X0)) ◇ X2) = X5 := superpose eq12 eq9
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq21 eq21
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq54 eq34


@[equational_result]
theorem Equation35278_implies_Equation2 (G : Type*) [Magma G] (h : Equation35278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation35279_implies_Equation2 (G : Type*) [Magma G] (h : Equation35279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35281_implies_Equation2 (G : Type*) [Magma G] (h : Equation35281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35282_implies_Equation2 (G : Type*) [Magma G] (h : Equation35282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35283_implies_Equation2 (G : Type*) [Magma G] (h : Equation35283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35284_implies_Equation2 (G : Type*) [Magma G] (h : Equation35284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35286_implies_Equation2 (G : Type*) [Magma G] (h : Equation35286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35287_implies_Equation2 (G : Type*) [Magma G] (h : Equation35287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35288_implies_Equation2 (G : Type*) [Magma G] (h : Equation35288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35289_implies_Equation2 (G : Type*) [Magma G] (h : Equation35289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35291_implies_Equation2 (G : Type*) [Magma G] (h : Equation35291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35292_implies_Equation2 (G : Type*) [Magma G] (h : Equation35292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35293_implies_Equation2 (G : Type*) [Magma G] (h : Equation35293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35294_implies_Equation2 (G : Type*) [Magma G] (h : Equation35294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35296_implies_Equation2 (G : Type*) [Magma G] (h : Equation35296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35297_implies_Equation2 (G : Type*) [Magma G] (h : Equation35297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35298_implies_Equation2 (G : Type*) [Magma G] (h : Equation35298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35299_implies_Equation2 (G : Type*) [Magma G] (h : Equation35299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35300_implies_Equation2 (G : Type*) [Magma G] (h : Equation35300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35302_implies_Equation2 (G : Type*) [Magma G] (h : Equation35302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X1) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq10
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq17 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq10 eq25
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation35303_implies_Equation2 (G : Type*) [Magma G] (h : Equation35303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X2) ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq9
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq94 eq35


@[equational_result]
theorem Equation35304_implies_Equation2 (G : Type*) [Magma G] (h : Equation35304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X3) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq9 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq45 eq36


@[equational_result]
theorem Equation35305_implies_Equation2 (G : Type*) [Magma G] (h : Equation35305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ ((X5 ◇ X4) ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X5 X6 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq9 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation35307_implies_Equation2 (G : Type*) [Magma G] (h : Equation35307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35308_implies_Equation2 (G : Type*) [Magma G] (h : Equation35308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35309_implies_Equation2 (G : Type*) [Magma G] (h : Equation35309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35310_implies_Equation2 (G : Type*) [Magma G] (h : Equation35310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35312_implies_Equation2 (G : Type*) [Magma G] (h : Equation35312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35313_implies_Equation2 (G : Type*) [Magma G] (h : Equation35313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35314_implies_Equation2 (G : Type*) [Magma G] (h : Equation35314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35315_implies_Equation2 (G : Type*) [Magma G] (h : Equation35315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35317_implies_Equation2 (G : Type*) [Magma G] (h : Equation35317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35318_implies_Equation2 (G : Type*) [Magma G] (h : Equation35318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35319_implies_Equation2 (G : Type*) [Magma G] (h : Equation35319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35320_implies_Equation2 (G : Type*) [Magma G] (h : Equation35320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35322_implies_Equation2 (G : Type*) [Magma G] (h : Equation35322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35323_implies_Equation2 (G : Type*) [Magma G] (h : Equation35323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35324_implies_Equation2 (G : Type*) [Magma G] (h : Equation35324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35325_implies_Equation2 (G : Type*) [Magma G] (h : Equation35325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35326_implies_Equation2 (G : Type*) [Magma G] (h : Equation35326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35328_implies_Equation2 (G : Type*) [Magma G] (h : Equation35328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation35329_implies_Equation2 (G : Type*) [Magma G] (h : Equation35329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq7 eq10
  have eq21 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq12 eq7
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation35330_implies_Equation2 (G : Type*) [Magma G] (h : Equation35330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation35331_implies_Equation2 (G : Type*) [Magma G] (h : Equation35331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35333_implies_Equation2 (G : Type*) [Magma G] (h : Equation35333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35334_implies_Equation2 (G : Type*) [Magma G] (h : Equation35334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35335_implies_Equation2 (G : Type*) [Magma G] (h : Equation35335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35336_implies_Equation2 (G : Type*) [Magma G] (h : Equation35336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35338_implies_Equation2 (G : Type*) [Magma G] (h : Equation35338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35339_implies_Equation2 (G : Type*) [Magma G] (h : Equation35339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35340_implies_Equation2 (G : Type*) [Magma G] (h : Equation35340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35341_implies_Equation2 (G : Type*) [Magma G] (h : Equation35341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35343_implies_Equation2 (G : Type*) [Magma G] (h : Equation35343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35344_implies_Equation2 (G : Type*) [Magma G] (h : Equation35344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35345_implies_Equation2 (G : Type*) [Magma G] (h : Equation35345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35346_implies_Equation2 (G : Type*) [Magma G] (h : Equation35346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35348_implies_Equation2 (G : Type*) [Magma G] (h : Equation35348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35349_implies_Equation2 (G : Type*) [Magma G] (h : Equation35349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35350_implies_Equation2 (G : Type*) [Magma G] (h : Equation35350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35351_implies_Equation2 (G : Type*) [Magma G] (h : Equation35351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35352_implies_Equation2 (G : Type*) [Magma G] (h : Equation35352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35354_implies_Equation2 (G : Type*) [Magma G] (h : Equation35354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation35355_implies_Equation2 (G : Type*) [Magma G] (h : Equation35355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation35356_implies_Equation2 (G : Type*) [Magma G] (h : Equation35356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35357_implies_Equation2 (G : Type*) [Magma G] (h : Equation35357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X5) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35358_implies_Equation2 (G : Type*) [Magma G] (h : Equation35358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X8 : G) : (X0 ◇ X8) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35360_implies_Equation2 (G : Type*) [Magma G] (h : Equation35360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35361_implies_Equation2 (G : Type*) [Magma G] (h : Equation35361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35362_implies_Equation2 (G : Type*) [Magma G] (h : Equation35362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35363_implies_Equation2 (G : Type*) [Magma G] (h : Equation35363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35364_implies_Equation2 (G : Type*) [Magma G] (h : Equation35364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35366_implies_Equation2 (G : Type*) [Magma G] (h : Equation35366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35367_implies_Equation2 (G : Type*) [Magma G] (h : Equation35367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35368_implies_Equation2 (G : Type*) [Magma G] (h : Equation35368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35369_implies_Equation2 (G : Type*) [Magma G] (h : Equation35369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35370_implies_Equation2 (G : Type*) [Magma G] (h : Equation35370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35372_implies_Equation2 (G : Type*) [Magma G] (h : Equation35372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35373_implies_Equation2 (G : Type*) [Magma G] (h : Equation35373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35374_implies_Equation2 (G : Type*) [Magma G] (h : Equation35374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35375_implies_Equation2 (G : Type*) [Magma G] (h : Equation35375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35376_implies_Equation2 (G : Type*) [Magma G] (h : Equation35376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35378_implies_Equation2 (G : Type*) [Magma G] (h : Equation35378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35379_implies_Equation2 (G : Type*) [Magma G] (h : Equation35379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35380_implies_Equation2 (G : Type*) [Magma G] (h : Equation35380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35381_implies_Equation2 (G : Type*) [Magma G] (h : Equation35381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35382_implies_Equation2 (G : Type*) [Magma G] (h : Equation35382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35384_implies_Equation2 (G : Type*) [Magma G] (h : Equation35384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35385_implies_Equation2 (G : Type*) [Magma G] (h : Equation35385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35386_implies_Equation2 (G : Type*) [Magma G] (h : Equation35386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35387_implies_Equation2 (G : Type*) [Magma G] (h : Equation35387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35388_implies_Equation2 (G : Type*) [Magma G] (h : Equation35388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35389_implies_Equation2 (G : Type*) [Magma G] (h : Equation35389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35595_implies_Equation2 (G : Type*) [Magma G] (h : Equation35595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq9 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation35598_implies_Equation2 (G : Type*) [Magma G] (h : Equation35598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X3) = X2 := superpose eq12 eq10
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation35600_implies_Equation2 (G : Type*) [Magma G] (h : Equation35600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = (((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))))) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq11 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X0 := superpose eq11 eq7
  have eq44 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (((X3 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0) ◇ X3) := superpose eq11 eq10
  have eq58 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1) = (((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ (((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1)))) := superpose eq10 eq11
  have eq66 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X2))))) = X1 := superpose eq10 eq15
  have eq67 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq15 eq15
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq67
  have eq98 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq81 eq14
  have eq115 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq81 eq98
  have eq120 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2))))) = X1 := superpose eq115 eq66
  have eq132 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (((X3 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) ◇ X3) := superpose eq115 eq44
  have eq133 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1) = (((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)))) ◇ X1))) := superpose eq115 eq58
  have eq143 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)))) := superpose eq115 eq12
  have eq177 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)))) = X1 := superpose eq115 eq120
  have eq178 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X1 := superpose eq115 eq177
  have eq193 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = (((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X3) := superpose eq115 eq132
  have eq194 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2))) ◇ X1) = (((X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2))) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq115 eq133
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq115 eq194
  have eq216 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) := superpose eq115 eq143
  have eq217 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq178 eq216
  have eq224 (X1 X3 : G) : ((X3 ◇ X1) ◇ X1) = (((X3 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq217 eq195
  have eq235 (X1 X3 : G) : ((X3 ◇ X1) ◇ X1) = X1 := superpose eq217 eq224
  have eq236 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq235 eq193
  have eq241 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq235 eq236
  have eq246 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq241 eq217
  have eq251 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq241 eq246
  have eq329 (X0 X1 : G) : X0 = X1 := superpose eq241 eq251
  have eq343 (X0 : G) : sK0 ≠ X0 := superpose eq329 eq8
  subsumption eq343 eq329


@[equational_result]
theorem Equation35601_implies_Equation2 (G : Type*) [Magma G] (h : Equation35601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq134 eq35


@[equational_result]
theorem Equation35602_implies_Equation2 (G : Type*) [Magma G] (h : Equation35602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) ◇ X4)) ◇ X5) := superpose eq7 eq7
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ X0) ◇ X5) := superpose eq7 eq9
  have eq14 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X0) ◇ X5) = X0 := superpose eq10 eq13
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq16 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X5) = X0 := superpose eq15 eq14
  have eq18 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq15 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation35605_implies_Equation2 (G : Type*) [Magma G] (h : Equation35605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = X0 := superpose eq12 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq16
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation35608_implies_Equation2 (G : Type*) [Magma G] (h : Equation35608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation35610_implies_Equation2 (G : Type*) [Magma G] (h : Equation35610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq10
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0)) = X2 := superpose eq11 eq11
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = X2 := superpose eq11 eq9
  have eq35 (X0 X1 X2 X4 : G) : ((((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ (X4 ◇ X4)) ◇ X2) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0)) = X4 := superpose eq11 eq10
  have eq56 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) = X1 := superpose eq9 eq28
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq11 eq28
  have eq82 (X0 X1 : G) : (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0)) ◇ X0) = X1 := superpose eq57 eq56
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X2 := superpose eq57 eq30
  have eq89 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ (X4 ◇ X4)) ◇ X2) ◇ (X1 ◇ X0)) = X4 := superpose eq57 eq35
  have eq116 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq57 eq82
  have eq117 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq57 eq116
  have eq128 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2))) = X3 := superpose eq87 eq10
  have eq138 (X0 X1 X2 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ X0)) = X4 := superpose eq87 eq89
  have eq139 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X3 := superpose eq138 eq128
  have eq178 (X0 X2 : G) : X0 = X2 := superpose eq139 eq117
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq199 eq178


@[equational_result]
theorem Equation35611_implies_Equation2 (G : Type*) [Magma G] (h : Equation35611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (((((((((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X4 ◇ X4)) ◇ X0) ◇ (X5 ◇ X5)) ◇ X4) ◇ X3) = X5 := superpose eq10 eq10
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq15 eq15
  have eq51 (X0 X3 X4 X5 : G) : ((((X4 ◇ X0) ◇ (X5 ◇ X5)) ◇ X4) ◇ X3) = X5 := superpose eq31 eq23
  have eq66 (X3 X4 X5 : G) : ((X5 ◇ X4) ◇ X3) = X5 := superpose eq31 eq51
  have eq71 (X0 X1 : G) : X0 = X1 := superpose eq15 eq66
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq75 eq71


@[equational_result]
theorem Equation35612_implies_Equation2 (G : Type*) [Magma G] (h : Equation35612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation35614_implies_Equation2 (G : Type*) [Magma G] (h : Equation35614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq10 eq11
  have eq32 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq23 eq7
  have eq44 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq23 eq32
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq44 eq44
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation35615_implies_Equation2 (G : Type*) [Magma G] (h : Equation35615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq96 eq30


@[equational_result]
theorem Equation35616_implies_Equation2 (G : Type*) [Magma G] (h : Equation35616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation35618_implies_Equation2 (G : Type*) [Magma G] (h : Equation35618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1))))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq10
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq9 eq10
  have eq32 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X0)) = X1 := superpose eq27 eq11
  have eq35 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq32 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq10 eq35
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq47 eq36


@[equational_result]
theorem Equation35620_implies_Equation2 (G : Type*) [Magma G] (h : Equation35620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35622_implies_Equation2 (G : Type*) [Magma G] (h : Equation35622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation35623_implies_Equation2 (G : Type*) [Magma G] (h : Equation35623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq43 eq27


@[equational_result]
theorem Equation35624_implies_Equation2 (G : Type*) [Magma G] (h : Equation35624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35626_implies_Equation2 (G : Type*) [Magma G] (h : Equation35626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq44 eq28


@[equational_result]
theorem Equation35627_implies_Equation2 (G : Type*) [Magma G] (h : Equation35627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq56 eq38


@[equational_result]
theorem Equation35628_implies_Equation2 (G : Type*) [Magma G] (h : Equation35628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq56 eq38


@[equational_result]
theorem Equation35629_implies_Equation2 (G : Type*) [Magma G] (h : Equation35629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35632_implies_Equation2 (G : Type*) [Magma G] (h : Equation35632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq155 eq56


@[equational_result]
theorem Equation35635_implies_Equation2 (G : Type*) [Magma G] (h : Equation35635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) ◇ X4) = X2 := superpose eq7 eq9
  have eq21 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq13
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq145 eq52


@[equational_result]
theorem Equation35637_implies_Equation2 (G : Type*) [Magma G] (h : Equation35637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = (((X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose eq11 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq31 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq26 eq7
  have eq33 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = (((X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X1)) ◇ X0) ◇ X1) := superpose eq26 eq10
  have eq34 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0))) := superpose eq26 eq12
  have eq58 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq31 eq31
  have eq79 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq14 eq58
  have eq238 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1))) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1))) = X1 := superpose eq33 eq31
  have eq251 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1))) = X1 := superpose eq34 eq238
  have eq252 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq251 eq34
  have eq253 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq252 eq26
  have eq279 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq253 eq79
  have eq281 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq279 eq14
  have eq289 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq281 eq58
  have eq301 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq281 eq289
  have eq302 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq281 eq301
  have eq372 (X0 X1 : G) : X0 = X1 := superpose eq302 eq281
  have eq374 (X0 : G) : sK0 ≠ X0 := superpose eq372 eq8
  subsumption eq374 eq372


@[equational_result]
theorem Equation35639_implies_Equation2 (G : Type*) [Magma G] (h : Equation35639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X4)) ◇ X5) := superpose eq7 eq7
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ X0) ◇ X5) := superpose eq7 eq9
  have eq14 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X0) ◇ X5) = X0 := superpose eq10 eq13
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq16 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X5) = X0 := superpose eq15 eq14
  have eq18 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq15 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation35642_implies_Equation2 (G : Type*) [Magma G] (h : Equation35642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq57 eq17


@[equational_result]
theorem Equation35645_implies_Equation2 (G : Type*) [Magma G] (h : Equation35645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq68 eq17


@[equational_result]
theorem Equation35647_implies_Equation2 (G : Type*) [Magma G] (h : Equation35647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X3)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq9
  have eq35 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = X1 := superpose eq26 eq25
  have eq77 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X3))) ◇ ((X0 ◇ X3) ◇ X4)) := superpose eq9 eq26
  have eq78 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq26 eq26
  have eq88 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq26 eq7
  have eq89 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) := superpose eq26 eq7
  have eq94 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3)) = ((((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq26 eq9
  have eq110 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq89 eq14
  have eq131 (X0 X1 X2 : G) : ((((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (X1 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq78 eq94
  have eq135 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq35
  have eq155 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq110 eq135
  have eq156 (X0 X1 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq26 eq155
  have eq176 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq156 eq156
  have eq323 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X0 := superpose eq26 eq176
  have eq435 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq323 eq131
  have eq436 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq323 eq88
  have eq439 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X1 := superpose eq436 eq435
  have eq450 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq439 eq78
  have eq462 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq450 eq77
  have eq479 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq462 eq7
  have eq529 (X0 X3 : G) : X0 = X3 := superpose eq479 eq479
  have eq554 (X0 : G) : sK0 ≠ X0 := superpose eq529 eq8
  subsumption eq554 eq529


@[equational_result]
theorem Equation35649_implies_Equation2 (G : Type*) [Magma G] (h : Equation35649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation35651_implies_Equation2 (G : Type*) [Magma G] (h : Equation35651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq133 eq41


@[equational_result]
theorem Equation35652_implies_Equation2 (G : Type*) [Magma G] (h : Equation35652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)))) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = (((((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) ◇ X4) ◇ ((X5 ◇ (X4 ◇ X5)) ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X2) ◇ X4))) := superpose eq10 eq10
  have eq20 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = ((X2 ◇ X4) ◇ ((X5 ◇ (X4 ◇ X5)) ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X2) ◇ X4))) := superpose eq7 eq12
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = (((X0 ◇ X2) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) := superpose eq10 eq9
  have eq60 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X4) ◇ ((X5 ◇ (X4 ◇ X5)) ◇ (X3 ◇ (X1 ◇ X3)))) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq30 eq30
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = (((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X1 ◇ X4))) ◇ ((X5 ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X5)) ◇ (X0 ◇ X1))) := superpose eq30 eq30
  have eq80 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq10 eq30
  have eq90 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X1 ◇ X4))) := superpose eq30 eq7
  have eq95 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ (X5 ◇ (X1 ◇ X5))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X5 ◇ (X1 ◇ X5))))) = X4 := superpose eq30 eq10
  have eq121 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)))) := superpose eq7 eq80
  have eq122 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) := superpose eq10 eq80
  have eq126 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ ((X1 ◇ X3) ◇ (X3 ◇ (X1 ◇ X3)))) = X3 := superpose eq30 eq80
  have eq134 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq80 eq80
  have eq156 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X2 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) := superpose eq7 eq122
  have eq206 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ (X4 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X4)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X4 ◇ (X2 ◇ X4))) = X2 := superpose eq20 eq80
  have eq232 (X2 X4 : G) : (X4 ◇ (X4 ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq206
  have eq265 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3))) = X2 := superpose eq232 eq10
  have eq273 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq232 eq80
  have eq293 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X2)) = X3 := superpose eq273 eq134
  have eq295 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq293 eq121
  have eq300 (X0 X1 X2 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X1 ◇ X4))) ◇ ((X5 ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X5)) ◇ (X0 ◇ X1))) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq293 eq67
  have eq302 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X1 ◇ X4))) := superpose eq293 eq90
  have eq328 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X2 ◇ (X0 ◇ X3)) := superpose eq293 eq156
  have eq344 (X0 X1 X2 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = (((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X1 ◇ X4))) ◇ ((X1 ◇ X4) ◇ (X0 ◇ X1))) := superpose eq293 eq300
  have eq350 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X4) ◇ ((X5 ◇ (X4 ◇ X5)) ◇ (X3 ◇ (X1 ◇ X3)))) = (((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq328 eq60
  have eq356 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ (X5 ◇ (X1 ◇ X5))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X5 ◇ (X1 ◇ X5))))) = X4 := superpose eq328 eq95
  have eq359 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ ((X1 ◇ X3) ◇ (X3 ◇ (X1 ◇ X3)))) = X3 := superpose eq328 eq126
  have eq363 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X4 ◇ (X1 ◇ X4))) := superpose eq328 eq302
  have eq365 (X0 X1 X2 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X1 ◇ X4))) ◇ ((X1 ◇ X4) ◇ (X0 ◇ X1))) := superpose eq328 eq344
  have eq370 (X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq328 eq265
  have eq428 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X4) ◇ ((X5 ◇ (X4 ◇ X5)) ◇ (X3 ◇ (X1 ◇ X3)))) = (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq293 eq350
  have eq436 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ (X5 ◇ (X1 ◇ X5))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X5 ◇ (X1 ◇ X5))))) = X4 := superpose eq293 eq356
  have eq439 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X3) ◇ (X3 ◇ (X1 ◇ X3)))) = X3 := superpose eq293 eq359
  have eq444 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X2 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X1 ◇ X4))) := superpose eq232 eq363
  have eq447 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X5 ◇ (X1 ◇ X5))))) = X4 := superpose eq444 eq436
  have eq448 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X3)))) = (((X4 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X4) ◇ (X4 ◇ X1)) := superpose eq444 eq428
  have eq449 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X3)))) = (X1 ◇ (X4 ◇ X1)) := superpose eq295 eq448
  have eq450 (X1 X4 : G) : ((X4 ◇ X1) ◇ (X1 ◇ (X4 ◇ X1))) = X4 := superpose eq449 eq447
  have eq453 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X3 := superpose eq450 eq439
  have eq459 (X0 X1 X2 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X1 ◇ X4))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq328 eq365
  have eq460 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq444 eq459
  have eq461 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq232 eq460
  have eq468 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq370 eq461
  have eq483 (X2 X4 : G) : (X4 ◇ X2) = X2 := superpose eq468 eq232
  have eq516 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = X3 := superpose eq483 eq453
  have eq527 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq483 eq516
  have eq528 (X0 X3 : G) : X0 = X3 := superpose eq527 eq527
  have eq533 (X0 : G) : sK0 ≠ X0 := superpose eq528 eq8
  subsumption eq533 eq528


@[equational_result]
theorem Equation35653_implies_Equation2 (G : Type*) [Magma G] (h : Equation35653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35655_implies_Equation2 (G : Type*) [Magma G] (h : Equation35655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq10 eq10
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq113 eq55


@[equational_result]
theorem Equation35657_implies_Equation2 (G : Type*) [Magma G] (h : Equation35657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq43 (X0 X6 : G) : X0 = X6 := superpose eq11 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq61 eq43


@[equational_result]
theorem Equation35659_implies_Equation2 (G : Type*) [Magma G] (h : Equation35659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X3)) = (((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)) ◇ X1) := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))) ◇ (X5 ◇ X5)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)) := superpose eq9 eq9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X5 ◇ X5)) ◇ (X3 ◇ X3)) = (((X3 ◇ X3) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0)) ◇ (X4 ◇ X4)) := superpose eq9 eq9
  have eq15 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = (((X0 ◇ X1) ◇ (X4 ◇ X4)) ◇ X0) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X4 ◇ X4)) = ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ X3)) = ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq9 eq7
  have eq35 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) = X1 := superpose eq24 eq23
  have eq37 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X4 ◇ X4)) := superpose eq31 eq22
  have eq40 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0))) := superpose eq9 eq10
  have eq41 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X2 ◇ X2)) = ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) ◇ X1) := superpose eq10 eq9
  have eq45 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X3)) = ((X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X0)) ◇ (X4 ◇ X4)) := superpose eq9 eq24
  have eq47 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) := superpose eq24 eq24
  have eq49 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq7 eq24
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq9 eq24
  have eq51 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq9 eq24
  have eq61 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X3)) = ((X0 ◇ X1) ◇ (X4 ◇ X4)) := superpose eq7 eq45
  have eq96 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq61
  have eq300 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq96 eq7
  have eq302 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := superpose eq96 eq7
  have eq304 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X4 ◇ X4)) ◇ X0) := superpose eq96 eq9
  have eq307 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) ◇ X0) := superpose eq96 eq35
  have eq373 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := superpose eq300 eq304
  have eq374 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq300 eq307
  have eq489 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq61 eq374
  have eq526 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) := superpose eq374 eq17
  have eq530 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq374 eq35
  have eq775 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq61 eq530
  have eq814 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ X2)) = (((X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) ◇ X0) := superpose eq530 eq11
  have eq831 (X0 X3 X4 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) ◇ X0) = X0 := superpose eq373 eq814
  have eq1167 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq17 eq31
  have eq2789 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) ◇ (X0 ◇ X0)) := superpose eq9 eq12
  have eq2819 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (X5 ◇ X5)) := superpose eq12 eq24
  have eq3066 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq302 eq2789
  have eq3092 (X0 X1 X4 X5 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X5 ◇ X5)) := superpose eq50 eq2819
  have eq3963 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X4 ◇ X4)) = (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq41
  have eq3983 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ X3)) = (((X1 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ X1)) ◇ (X5 ◇ X5)) ◇ X1) := superpose eq41 eq11
  have eq4160 (X0 X1 X4 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X4 ◇ X4)) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq302 eq3963
  have eq4178 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = (((X1 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ X1)) ◇ (X5 ◇ X5)) ◇ X1) := superpose eq10 eq3983
  have eq4745 (X0 X1 X2 X3 X5 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X5 ◇ X5)) := superpose eq489 eq13
  have eq5071 (X0 X1 X2 X5 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X5 ◇ X5)) = X2 := superpose eq302 eq4745
  have eq5090 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq5071 eq3066
  have eq5092 (X0 X1 X4 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4))) = X1 := superpose eq5071 eq3092
  have eq5098 (X0 X1 X4 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X4 ◇ X4)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq5090 eq4160
  have eq5102 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := superpose eq5098 eq41
  have eq5138 (X0 X1 X3 X5 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = (((X1 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) ◇ (X5 ◇ X5)) ◇ X1) := superpose eq5102 eq4178
  have eq5146 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq5138
  have eq5171 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq5146 eq1167
  have eq6182 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X4 ◇ X4)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) = X3 := superpose eq489 eq15
  have eq6273 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))))) = ((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X1) ◇ (((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))))) := superpose eq15 eq40
  have eq6274 (X2 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) = X3 := superpose eq775 eq6182
  have eq6321 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))) = ((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))))) := superpose eq831 eq6273
  have eq6322 (X0 X2 : G) : ((((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ X0) = X0 := superpose eq6274 eq6321
  have eq6381 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq6322 eq24
  have eq8201 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) = X1 := superpose eq49 eq6322
  have eq9005 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X3 ◇ X3))) = X0 := superpose eq526 eq5092
  have eq9758 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1)) = X0 := superpose eq24 eq47
  have eq9947 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq8201 eq9758
  have eq10016 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq9947 eq5171
  have eq10028 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq775 eq10016
  have eq10029 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq10028 eq51
  have eq10031 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq10029 eq9005
  have eq10057 (X1 X3 X4 : G) : ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ (X4 ◇ X4)) = X1 := superpose eq10031 eq37
  have eq10058 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ X2)) := superpose eq10031 eq49
  have eq10504 (X1 X4 : G) : ((X1 ◇ X1) ◇ (X4 ◇ X4)) = X1 := superpose eq10031 eq10057
  have eq10505 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq10504 eq6381
  have eq10511 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq10505 eq10058
  have eq10662 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq10511 eq300
  have eq11319 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10511 eq10662
  have eq11320 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) = X0 := superpose eq11319 eq24
  have eq11324 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq11319 eq10031
  have eq11359 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq11324 eq11320
  have eq11384 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11319 eq11359
  have eq11387 (X0 X3 : G) : X0 = X3 := superpose eq11384 eq11384
  have eq11393 (X0 : G) : sK0 ≠ X0 := superpose eq11387 eq8
  subsumption eq11393 eq11387


@[equational_result]
theorem Equation35661_implies_Equation2 (G : Type*) [Magma G] (h : Equation35661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation35663_implies_Equation2 (G : Type*) [Magma G] (h : Equation35663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq44 eq28


@[equational_result]
theorem Equation35664_implies_Equation2 (G : Type*) [Magma G] (h : Equation35664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X2) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq79 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq187 eq79


@[equational_result]
theorem Equation35665_implies_Equation2 (G : Type*) [Magma G] (h : Equation35665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation35666_implies_Equation2 (G : Type*) [Magma G] (h : Equation35666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35668_implies_Equation2 (G : Type*) [Magma G] (h : Equation35668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq10
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq10 eq7
  have eq72 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq13 eq15
  have eq293 (X0 X1 X3 : G) : (((X3 ◇ X1) ◇ (X0 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq30
  have eq302 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq30
  have eq364 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq23 eq293
  have eq407 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq364 eq302
  have eq411 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq364 eq72
  have eq504 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq407 eq13
  have eq511 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq407 eq411
  have eq512 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq511
  have eq518 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq512 eq504
  have eq523 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq518 eq512
  have eq524 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq523 eq364
  have eq525 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := superpose eq523 eq7
  have eq527 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq523 eq11
  have eq546 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq524 eq527
  have eq547 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq546 eq524
  have eq548 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq547 eq525
  have eq551 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq547 eq548
  have eq569 (X0 X2 : G) : X0 = X2 := superpose eq551 eq551
  have eq571 (X0 : G) : sK0 ≠ X0 := superpose eq569 eq8
  subsumption eq571 eq569


@[equational_result]
theorem Equation35669_implies_Equation2 (G : Type*) [Magma G] (h : Equation35669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X0)))) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X3) := superpose eq10 eq9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = ((X2 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq11 eq12
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq11 eq10
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ X0) ◇ X3) := superpose eq14 eq13
  have eq17 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq14 eq16
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq17 eq14
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq11 eq18
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq27 eq19


@[equational_result]
theorem Equation35670_implies_Equation2 (G : Type*) [Magma G] (h : Equation35670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation35672_implies_Equation2 (G : Type*) [Magma G] (h : Equation35672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X2)) ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq24 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq20 eq7
  have eq25 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = (((X1 ◇ X0) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X1)) ◇ X1) := superpose eq20 eq9
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)))) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq20 eq10
  have eq41 (X0 X1 : G) : (((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq24 eq24
  have eq42 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq24 eq24
  have eq51 (X0 X1 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq41 eq41
  have eq73 (X0 X1 X2 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X1) = ((X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ X0) := superpose eq24 eq20
  have eq86 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) = ((X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ X0) := superpose eq20 eq73
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ X0) := superpose eq24 eq86
  have eq107 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X2 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ X2) := superpose eq24 eq25
  have eq114 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2))) ◇ ((X2 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2))) = X2 := superpose eq25 eq24
  have eq134 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq42 eq87
  have eq146 (X0 X1 X2 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2)) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq87 eq42
  have eq151 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2)) := superpose eq42 eq146
  have eq160 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose eq24 eq35
  have eq161 (X0 X1 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq41 eq35
  have eq235 (X0 X1 X2 : G) : (X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1)) = ((X0 ◇ ((X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1)) ◇ ((X2 ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)))) ◇ ((X2 ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X0))) := superpose eq41 eq107
  have eq279 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X2)) = X0 := superpose eq24 eq151
  have eq292 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X2)) := superpose eq20 eq151
  have eq319 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq24 eq292
  have eq324 (X0 X1 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq319 eq161
  have eq326 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose eq319 eq160
  have eq365 (X0 X1 X2 : G) : (X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1)) = ((X0 ◇ ((X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X0))) := superpose eq319 eq235
  have eq377 (X0 X1 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq324 eq51
  have eq378 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose eq319 eq326
  have eq379 (X0 X1 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq378 eq377
  have eq384 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq379 eq41
  have eq390 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X0 := superpose eq379 eq279
  have eq432 (X0 X1 X2 : G) : (X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1)) = ((X0 ◇ ((X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq379 eq365
  have eq471 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq384 eq134
  have eq510 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq390 eq471
  have eq519 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X2 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X2 := superpose eq510 eq114
  have eq547 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq510 eq432
  have eq705 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq510 eq519
  have eq706 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X2 := superpose eq510 eq705
  have eq707 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X2 := superpose eq510 eq706
  have eq708 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X2 := superpose eq510 eq707
  have eq709 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq510 eq708
  have eq710 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq510 eq709
  have eq803 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq510 eq547
  have eq804 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1)) := superpose eq710 eq803
  have eq805 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) := superpose eq510 eq804
  have eq806 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq510 eq805
  have eq807 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X2 ◇ X0) := superpose eq510 eq806
  have eq808 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X2 := superpose eq510 eq807
  have eq809 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq510 eq808
  have eq818 (X0 X3 : G) : X0 = X3 := superpose eq809 eq809
  have eq851 (X0 : G) : sK0 ≠ X0 := superpose eq818 eq8
  subsumption eq851 eq818


@[equational_result]
theorem Equation35674_implies_Equation2 (G : Type*) [Magma G] (h : Equation35674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X5) = X3 := superpose eq12 eq10
  have eq18 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation35676_implies_Equation2 (G : Type*) [Magma G] (h : Equation35676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq10
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq7
  have eq24 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq19 eq17
  have eq27 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq19 eq24
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq19 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation35677_implies_Equation2 (G : Type*) [Magma G] (h : Equation35677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq141 eq49


@[equational_result]
theorem Equation35678_implies_Equation2 (G : Type*) [Magma G] (h : Equation35678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq9 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation35680_implies_Equation2 (G : Type*) [Magma G] (h : Equation35680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ X5)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq12
  have eq30 (X0 X1 X2 X3 X4 X5 X9 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (((X3 ◇ X5) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X9))) = X3 := superpose eq10 eq10
  have eq40 (X0 X1 X2 X3 X7 : G) : (X2 ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X7)) ◇ X1) := superpose eq10 eq7
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = (((X4 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) ◇ X4) := superpose eq12 eq9
  have eq104 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) := superpose eq40 eq85
  have eq107 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq104 eq7
  have eq153 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq12 eq107
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq153 eq16
  have eq164 (X0 X1 X2 X3 X4 X5 X9 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ ((X3 ◇ X5) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X9))) = X3 := superpose eq161 eq30
  have eq204 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X5)) = X3 := superpose eq161 eq164
  have eq205 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X3) = X3 := superpose eq161 eq204
  have eq206 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = X3 := superpose eq161 eq205
  have eq207 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq161 eq206
  have eq264 (X0 X1 : G) : X0 = X1 := superpose eq161 eq207
  have eq266 (X0 : G) : sK0 ≠ X0 := superpose eq264 eq8
  subsumption eq266 eq264


@[equational_result]
theorem Equation35681_implies_Equation2 (G : Type*) [Magma G] (h : Equation35681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5)) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X2 ◇ X5)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = (((X1 ◇ X0) ◇ X0) ◇ X3) := superpose eq10 eq9
  have eq14 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq10 eq13
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq14 eq15
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation35682_implies_Equation2 (G : Type*) [Magma G] (h : Equation35682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = X0 := superpose eq12 eq7
  have eq21 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq15
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation35683_implies_Equation2 (G : Type*) [Magma G] (h : Equation35683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X6)) ◇ X7) := superpose eq7 eq7
  have eq10 (X0 X4 X6 X7 : G) : ((X0 ◇ (X4 ◇ X6)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X7 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = (((X1 ◇ X0) ◇ X0) ◇ X7) := superpose eq7 eq9
  have eq14 (X0 X1 X7 : G) : (((X1 ◇ X0) ◇ X0) ◇ X7) = X0 := superpose eq10 eq13
  have eq15 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq10 eq7
  have eq16 (X0 X1 X7 : G) : ((X1 ◇ X0) ◇ X7) = X0 := superpose eq15 eq14
  have eq18 (X0 X1 X7 : G) : (X1 ◇ X7) = X0 := superpose eq15 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation35686_implies_Equation2 (G : Type*) [Magma G] (h : Equation35686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X0)))) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X3 ◇ X4)) ◇ X0) ◇ X4) = X3 := superpose eq10 eq7
  have eq102 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq7
  have eq207 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq20
  have eq307 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = (((X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0))))) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0))))) ◇ (X1 ◇ X2))) := superpose eq7 eq102
  have eq373 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq207
  have eq440 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq373 eq307
  have eq448 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq440 eq7
  have eq1092 (X0 X2 : G) : X0 = X2 := superpose eq448 eq448
  have eq1094 (X0 : G) : sK0 ≠ X0 := superpose eq1092 eq8
  subsumption eq1094 eq1092


@[equational_result]
theorem Equation35687_implies_Equation2 (G : Type*) [Magma G] (h : Equation35687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation35689_implies_Equation2 (G : Type*) [Magma G] (h : Equation35689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X2)) = (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X3) ◇ X4)) ◇ (X2 ◇ X2)) = (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X1 ◇ X5)) ◇ (X3 ◇ (X1 ◇ X5)))) ◇ (X3 ◇ (X1 ◇ X5))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X2 ◇ X2)) = ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X5) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ X2)) ◇ X2) := superpose eq9 eq7
  have eq33 (X0 X1 X3 X5 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X1 ◇ X5)) ◇ (X3 ◇ (X1 ◇ X5)))) ◇ (X3 ◇ (X1 ◇ X5))) = X3 := superpose eq24 eq21
  have eq34 (X0 X1 X5 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X5) = X1 := superpose eq24 eq23
  have eq37 (X1 X3 X5 : G) : (X1 ◇ (X3 ◇ (X1 ◇ X5))) = X3 := superpose eq34 eq33
  have eq39 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = ((X0 ◇ X1) ◇ X2) := superpose eq24 eq28
  have eq47 (X0 X1 X2 X3 : G) : ((X2 ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X3)))) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X3)))))) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X3))))) = X2 := superpose eq9 eq10
  have eq63 (X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X1) = X2 := superpose eq34 eq47
  have eq69 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X5) = X1 := superpose eq63 eq34
  have eq86 (X1 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = X1 := superpose eq69 eq39
  have eq94 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq86 eq37
  have eq100 (X0 X2 : G) : X0 = X2 := superpose eq94 eq94
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq108 eq100


@[equational_result]
theorem Equation35691_implies_Equation2 (G : Type*) [Magma G] (h : Equation35691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation35694_implies_Equation2 (G : Type*) [Magma G] (h : Equation35694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X3)) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ X3) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq11
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) := superpose eq59 eq9
  have eq78 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq59 eq7
  have eq88 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = X2 := superpose eq59 eq11
  have eq91 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) ◇ X2) = X2 := superpose eq59 eq11
  have eq106 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq78 eq77
  have eq107 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq106 eq78
  have eq119 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq7 eq91
  have eq120 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq107 eq119
  have eq121 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq120 eq88
  have eq177 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq120 eq121
  have eq178 (X0 X1 : G) : X0 = X1 := superpose eq107 eq177
  have eq186 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq186 eq178


@[equational_result]
theorem Equation35695_implies_Equation2 (G : Type*) [Magma G] (h : Equation35695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation35697_implies_Equation2 (G : Type*) [Magma G] (h : Equation35697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4)) = (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X3 ◇ ((X4 ◇ X5) ◇ X6)) ◇ (X3 ◇ X7)) = (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X4 ◇ (X1 ◇ X8)) ◇ X9)) ◇ (X4 ◇ (X1 ◇ X8))) := superpose eq9 eq9
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ ((X1 ◇ X4) ◇ X5)) ◇ (X3 ◇ X6)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X7) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X3 ◇ (X1 ◇ X4)) ◇ (X5 ◇ X6)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X3 ◇ (X1 ◇ X4))) = X5 := superpose eq9 eq7
  have eq41 (X0 X1 X2 X7 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X7) = X1 := superpose eq29 eq28
  have eq42 (X0 X1 X2 X4 X8 X9 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X4 ◇ (X1 ◇ X8)) ◇ X9)) ◇ (X4 ◇ (X1 ◇ X8))) = X4 := superpose eq29 eq24
  have eq43 (X1 X4 X8 : G) : (X1 ◇ (X4 ◇ (X1 ◇ X8))) = X4 := superpose eq41 eq42
  have eq84 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq43 eq43
  have eq120 (X0 X1 X3 X4 X5 X6 : G) : ((((X3 ◇ (X1 ◇ X4)) ◇ (X5 ◇ X6)) ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X4))) = X5 := superpose eq84 eq33
  have eq157 (X0 X1 X5 X6 : G) : (((X1 ◇ (X5 ◇ X6)) ◇ (X0 ◇ X0)) ◇ X1) = X5 := superpose eq84 eq120
  have eq158 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq84 eq157
  have eq159 (X0 X3 : G) : X0 = X3 := superpose eq158 eq158
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq161 eq159


@[equational_result]
theorem Equation35698_implies_Equation2 (G : Type*) [Magma G] (h : Equation35698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4)) = (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ X3) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X4 ◇ ((X5 ◇ X6) ◇ X7)) ◇ (X4 ◇ X8)) = (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X5 ◇ (X1 ◇ X3)) ◇ X9)) ◇ X7) := superpose eq9 eq9
  have eq30 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ ((X1 ◇ X3) ◇ X5)) ◇ (X4 ◇ X6)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X5) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X4 ◇ (X1 ◇ X3)) ◇ X6)) ◇ X5) = X4 := superpose eq9 eq7
  have eq43 (X4 X5 X6 X7 X8 : G) : ((X4 ◇ ((X5 ◇ X6) ◇ X7)) ◇ (X4 ◇ X8)) = X5 := superpose eq35 eq25
  have eq46 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X5) = X1 := superpose eq43 eq30
  have eq48 (X1 X4 X5 : G) : (X1 ◇ X5) = X4 := superpose eq46 eq35
  have eq87 (X0 X4 : G) : X0 = X4 := superpose eq7 eq48
  have eq208 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq208 eq87


@[equational_result]
theorem Equation35699_implies_Equation2 (G : Type*) [Magma G] (h : Equation35699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq78 eq13


@[equational_result]
theorem Equation35700_implies_Equation2 (G : Type*) [Magma G] (h : Equation35700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation35703_implies_Equation2 (G : Type*) [Magma G] (h : Equation35703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq10
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq117 eq36


@[equational_result]
theorem Equation35704_implies_Equation2 (G : Type*) [Magma G] (h : Equation35704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35708_implies_Equation2 (G : Type*) [Magma G] (h : Equation35708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq71 eq13


@[equational_result]
theorem Equation35711_implies_Equation2 (G : Type*) [Magma G] (h : Equation35711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation35712_implies_Equation2 (G : Type*) [Magma G] (h : Equation35712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35714_implies_Equation2 (G : Type*) [Magma G] (h : Equation35714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq12
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq180 eq71


@[equational_result]
theorem Equation35715_implies_Equation2 (G : Type*) [Magma G] (h : Equation35715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X3 ◇ X5)) ◇ X3) = X2 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation35716_implies_Equation2 (G : Type*) [Magma G] (h : Equation35716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation35717_implies_Equation2 (G : Type*) [Magma G] (h : Equation35717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35719_implies_Equation2 (G : Type*) [Magma G] (h : Equation35719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq30 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq12
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq30
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq126 eq39


@[equational_result]
theorem Equation35720_implies_Equation2 (G : Type*) [Magma G] (h : Equation35720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X5 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35721_implies_Equation2 (G : Type*) [Magma G] (h : Equation35721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ (X5 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq127 eq42


@[equational_result]
theorem Equation35722_implies_Equation2 (G : Type*) [Magma G] (h : Equation35722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : ((X0 ◇ (X6 ◇ X4)) ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35724_implies_Equation2 (G : Type*) [Magma G] (h : Equation35724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq11
  have eq81 (X0 X4 : G) : X0 = X4 := superpose eq16 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq168 eq81


@[equational_result]
theorem Equation35725_implies_Equation2 (G : Type*) [Magma G] (h : Equation35725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq7 eq11
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq168 eq65


@[equational_result]
theorem Equation35726_implies_Equation2 (G : Type*) [Magma G] (h : Equation35726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X3 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X5 ◇ X2)) ◇ X5) = X1 := superpose eq12 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) = X2 := superpose eq12 eq7
  have eq24 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ X4) = X2 := superpose eq12 eq22
  have eq26 (X1 X2 X5 : G) : (X2 ◇ X5) = X1 := superpose eq24 eq21
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq43 eq35


@[equational_result]
theorem Equation35727_implies_Equation2 (G : Type*) [Magma G] (h : Equation35727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35729_implies_Equation2 (G : Type*) [Magma G] (h : Equation35729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation35730_implies_Equation2 (G : Type*) [Magma G] (h : Equation35730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X5 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation35731_implies_Equation2 (G : Type*) [Magma G] (h : Equation35731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X5 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation35732_implies_Equation2 (G : Type*) [Magma G] (h : Equation35732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35734_implies_Equation2 (G : Type*) [Magma G] (h : Equation35734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation35735_implies_Equation2 (G : Type*) [Magma G] (h : Equation35735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X2) = X0 := superpose eq11 eq7
  have eq18 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq13
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation35736_implies_Equation2 (G : Type*) [Magma G] (h : Equation35736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ (X5 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq46 eq29


@[equational_result]
theorem Equation35737_implies_Equation2 (G : Type*) [Magma G] (h : Equation35737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35739_implies_Equation2 (G : Type*) [Magma G] (h : Equation35739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq53 eq35


@[equational_result]
theorem Equation35740_implies_Equation2 (G : Type*) [Magma G] (h : Equation35740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35741_implies_Equation2 (G : Type*) [Magma G] (h : Equation35741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X6 X7 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X6) = X3 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation35742_implies_Equation2 (G : Type*) [Magma G] (h : Equation35742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35743_implies_Equation2 (G : Type*) [Magma G] (h : Equation35743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X7 : G) : (X0 ◇ X7) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35746_implies_Equation2 (G : Type*) [Magma G] (h : Equation35746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq9
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq12
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq142 eq45


@[equational_result]
theorem Equation35749_implies_Equation2 (G : Type*) [Magma G] (h : Equation35749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X3 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ X0))) ◇ X4) = X2 := superpose eq7 eq12
  have eq30 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq17
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq166 eq56


@[equational_result]
theorem Equation35751_implies_Equation2 (G : Type*) [Magma G] (h : Equation35751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) = (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)))) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4)) ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X4)) = (((X1 ◇ (X1 ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X4)))) ◇ X0) ◇ X1) := superpose eq9 eq7
  have eq27 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = (((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) := superpose eq9 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = ((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ ((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X4))) := superpose eq9 eq11
  have eq38 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq11 eq11
  have eq46 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq7
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq10
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) ◇ X1) := superpose eq11 eq7
  have eq60 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq11 eq38
  have eq64 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = ((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ ((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X4))) := superpose eq46 eq35
  have eq71 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq46 eq60
  have eq72 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq46 eq11
  have eq74 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq46 eq48
  have eq102 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq46 eq7
  have eq104 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq46 eq10
  have eq115 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq54 eq104
  have eq116 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq46 eq115
  have eq153 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) = ((((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ ((((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ ((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0)) ◇ (((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ X5))) := superpose eq18 eq72
  have eq193 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = (((((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq46 eq27
  have eq228 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq46 eq193
  have eq232 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq116 eq102
  have eq248 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq116 eq72
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq116 eq102
  have eq257 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq116 eq248
  have eq259 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq251 eq228
  have eq262 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq102 eq259
  have eq263 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq72 eq262
  have eq269 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq263 eq257
  have eq271 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq232 eq269
  have eq277 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) = ((((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ (((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ (((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ X5))) := superpose eq271 eq153
  have eq282 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = ((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X4))) := superpose eq271 eq64
  have eq295 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq271 eq71
  have eq298 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq271 eq74
  have eq306 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq271 eq102
  have eq334 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq306 eq298
  have eq340 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq271 eq334
  have eq341 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq295 eq340
  have eq347 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) = ((((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ ((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)))) ◇ X0)) := superpose eq341 eq277
  have eq358 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = ((((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) := superpose eq341 eq282
  have eq380 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4)) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X0)) = X1 := superpose eq341 eq16
  have eq391 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X0 := superpose eq341 eq54
  have eq440 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (((X4 ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ (X4 ◇ X0)) := superpose eq341 eq347
  have eq441 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (((X4 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ (X4 ◇ X0)) := superpose eq341 eq440
  have eq458 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = (((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) := superpose eq341 eq358
  have eq504 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4)) ◇ (X1 ◇ X0)) = X1 := superpose eq341 eq380
  have eq517 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq341 eq391
  have eq518 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := superpose eq517 eq458
  have eq529 (X0 X4 : G) : (X4 ◇ X0) = (((X4 ◇ X0) ◇ X0) ◇ (X4 ◇ X0)) := superpose eq518 eq441
  have eq540 (X0 X4 : G) : (X4 ◇ X0) = X0 := superpose eq517 eq529
  have eq543 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X4)) ◇ (X1 ◇ X0)) = X1 := superpose eq540 eq504
  have eq556 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X0) = X1 := superpose eq540 eq543
  have eq557 (X0 X1 X4 : G) : ((X1 ◇ X4) ◇ X0) = X1 := superpose eq540 eq556
  have eq558 (X0 X1 X4 : G) : (X4 ◇ X0) = X1 := superpose eq540 eq557
  have eq559 (X0 X3 : G) : X0 = X3 := superpose eq558 eq558
  have eq561 (X0 : G) : sK0 ≠ X0 := superpose eq559 eq8
  subsumption eq561 eq559


@[equational_result]
theorem Equation35752_implies_Equation2 (G : Type*) [Magma G] (h : Equation35752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) = (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)))) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X2) = X0 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X4)) = (((((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X4)))) ◇ X2) ◇ X0) ◇ X4) := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ ((((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X3) ◇ (X0 ◇ X4)))) ◇ X0) = (((X5 ◇ (X5 ◇ ((X1 ◇ (X1 ◇ ((((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X3) ◇ (X0 ◇ X4)))) ◇ X0))) ◇ ((((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X3) ◇ (X0 ◇ X4))) ◇ X4) := superpose eq9 eq10
  have eq37 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq15 eq15
  have eq38 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) = X1 := superpose eq15 eq7
  have eq83 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq37
  have eq164 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq83 eq7
  have eq179 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq83 eq15
  have eq194 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq83 eq179
  have eq335 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq83 eq16
  have eq365 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq335
  have eq366 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq15 eq365
  have eq367 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq83 eq366
  have eq368 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq194 eq367
  have eq379 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq368 eq164
  have eq409 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq15 eq379
  have eq411 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X1 := superpose eq409 eq38
  have eq464 (X0 X1 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X4))) ◇ X0) = (((X5 ◇ (X5 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X4))) ◇ X0))) ◇ (X0 ◇ X4)) ◇ X4) := superpose eq409 eq24
  have eq597 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq409 eq411
  have eq681 (X0 X1 X4 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X4))) ◇ X0) = X4 := superpose eq409 eq464
  have eq682 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X0) = X4 := superpose eq409 eq681
  have eq683 (X0 X4 : G) : ((X0 ◇ X4) ◇ X0) = X4 := superpose eq409 eq682
  have eq684 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq409 eq683
  have eq1017 (X0 X1 : G) : X0 = X1 := superpose eq684 eq597
  have eq1022 (X0 : G) : sK0 ≠ X0 := superpose eq1017 eq8
  subsumption eq1022 eq1017


@[equational_result]
theorem Equation35753_implies_Equation2 (G : Type*) [Magma G] (h : Equation35753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35756_implies_Equation2 (G : Type*) [Magma G] (h : Equation35756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation35759_implies_Equation2 (G : Type*) [Magma G] (h : Equation35759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq12
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq29 eq19


@[equational_result]
theorem Equation35761_implies_Equation2 (G : Type*) [Magma G] (h : Equation35761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ X0) ◇ (((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ X0) ◇ X5)) ◇ X4) ◇ ((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ X0)) = X5 := superpose eq9 eq10
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq11
  have eq69 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq30 eq7
  have eq74 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X2)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq30 eq11
  have eq108 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq69
  have eq212 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq108 eq108
  have eq372 (X0 X1 X2 X3 X4 : G) : (((((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) ◇ X0) ◇ (((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) ◇ X0) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ ((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) ◇ X0)) = X4 := superpose eq9 eq24
  have eq508 (X0 X2 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq30 eq212
  have eq556 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq212 eq7
  have eq1158 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq508 eq7
  have eq1188 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq1158
  have eq1190 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq1188 eq74
  have eq1237 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq1188 eq1190
  have eq1288 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq1237 eq556
  have eq1371 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq1188 eq1288
  have eq1372 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq1188 eq1371
  have eq1373 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq1188 eq1372
  have eq1375 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) ◇ ((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0)) = X4 := superpose eq1373 eq372
  have eq1746 (X0 X1 X2 X3 X4 : G) : (((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3))) = X4 := superpose eq1373 eq1375
  have eq1747 (X0 X1 X2 X4 : G) : ((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1)) = X4 := superpose eq1373 eq1746
  have eq1748 (X0 X1 X2 X4 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) = X4 := superpose eq1373 eq1747
  have eq1749 (X0 X1 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X4)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) = X4 := superpose eq1373 eq1748
  have eq1750 (X0 X4 : G) : (((X0 ◇ (X0 ◇ X4)) ◇ X0) ◇ X0) = X4 := superpose eq1373 eq1749
  have eq1751 (X0 X4 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X0) = X4 := superpose eq1373 eq1750
  have eq1752 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq1373 eq1751
  have eq5889 (X0 X2 : G) : X0 = X2 := superpose eq1752 eq1752
  have eq5891 (X0 : G) : sK0 ≠ X0 := superpose eq5889 eq8
  subsumption eq5891 eq5889


@[equational_result]
theorem Equation35763_implies_Equation2 (G : Type*) [Magma G] (h : Equation35763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq7 eq12
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq31 eq19


@[equational_result]
theorem Equation35765_implies_Equation2 (G : Type*) [Magma G] (h : Equation35765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq7
  have eq23 (X0 X1 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) = X1 := superpose eq10 eq11
  have eq27 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq11 eq10
  have eq29 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq27 eq23
  have eq32 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq10 eq29
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq29 eq10
  have eq46 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := superpose eq29 eq9
  have eq66 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = (((X0 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) ◇ X0) := superpose eq10 eq9
  have eq77 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := superpose eq29 eq46
  have eq78 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq29 eq77
  have eq88 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq33 eq33
  have eq105 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq88 eq32
  have eq109 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) := superpose eq88 eq66
  have eq112 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq88 eq10
  have eq128 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq105 eq78
  have eq131 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq112 eq109
  have eq132 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq131 eq128
  have eq145 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq132 eq131
  have eq148 (X0 X1 : G) : X0 = X1 := superpose eq145 eq132
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq158 eq148


@[equational_result]
theorem Equation35767_implies_Equation2 (G : Type*) [Magma G] (h : Equation35767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X4 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq14 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation35769_implies_Equation2 (G : Type*) [Magma G] (h : Equation35769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq10 eq10
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq92 eq56


@[equational_result]
theorem Equation35771_implies_Equation2 (G : Type*) [Magma G] (h : Equation35771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation35775_implies_Equation2 (G : Type*) [Magma G] (h : Equation35775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X0) ◇ (X4 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq62 eq41


@[equational_result]
theorem Equation35777_implies_Equation2 (G : Type*) [Magma G] (h : Equation35777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq47 eq29


@[equational_result]
theorem Equation35778_implies_Equation2 (G : Type*) [Magma G] (h : Equation35778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation35779_implies_Equation2 (G : Type*) [Magma G] (h : Equation35779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X5) = X3 := superpose eq10 eq9
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation35780_implies_Equation2 (G : Type*) [Magma G] (h : Equation35780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation35783_implies_Equation2 (G : Type*) [Magma G] (h : Equation35783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35786_implies_Equation2 (G : Type*) [Magma G] (h : Equation35786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X0))) ◇ X4) = X2 := superpose eq7 eq12
  have eq28 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq17
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq28
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq183 eq70


@[equational_result]
theorem Equation35788_implies_Equation2 (G : Type*) [Magma G] (h : Equation35788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) := superpose eq7 eq9
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq10 eq10
  have eq54 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)) = X1 := superpose eq9 eq10
  have eq65 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq7 eq54
  have eq66 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq65 eq52
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) := superpose eq65 eq16
  have eq68 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq65 eq10
  have eq69 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq65 eq7
  have eq83 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq65 eq66
  have eq84 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X2 ◇ X2) ◇ X0) ◇ X2) := superpose eq65 eq67
  have eq85 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := superpose eq65 eq84
  have eq86 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq65 eq68
  have eq87 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq86 eq85
  have eq88 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq87 eq83
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq65 eq88
  have eq92 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq89 eq69
  have eq93 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq89 eq92
  have eq94 (X0 X3 : G) : X0 = X3 := superpose eq93 eq93
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq96 eq94


@[equational_result]
theorem Equation35789_implies_Equation2 (G : Type*) [Magma G] (h : Equation35789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := superpose eq11 eq7
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := superpose eq11 eq15
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq20 eq20
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq20 eq26
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq64 eq27


@[equational_result]
theorem Equation35790_implies_Equation2 (G : Type*) [Magma G] (h : Equation35790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35793_implies_Equation2 (G : Type*) [Magma G] (h : Equation35793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq12
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq31 eq20


@[equational_result]
theorem Equation35795_implies_Equation2 (G : Type*) [Magma G] (h : Equation35795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation35796_implies_Equation2 (G : Type*) [Magma G] (h : Equation35796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35798_implies_Equation2 (G : Type*) [Magma G] (h : Equation35798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35799_implies_Equation2 (G : Type*) [Magma G] (h : Equation35799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35800_implies_Equation2 (G : Type*) [Magma G] (h : Equation35800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35802_implies_Equation2 (G : Type*) [Magma G] (h : Equation35802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq40 eq16


@[equational_result]
theorem Equation35803_implies_Equation2 (G : Type*) [Magma G] (h : Equation35803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) := superpose eq10 eq9
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq21
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq31 eq7
  have eq34 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq11
  have eq81 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq32 eq32
  have eq82 (X0 X1 : G) : X0 = X1 := superpose eq34 eq81
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq114 eq82


@[equational_result]
theorem Equation35804_implies_Equation2 (G : Type*) [Magma G] (h : Equation35804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35806_implies_Equation2 (G : Type*) [Magma G] (h : Equation35806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35807_implies_Equation2 (G : Type*) [Magma G] (h : Equation35807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35808_implies_Equation2 (G : Type*) [Magma G] (h : Equation35808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35810_implies_Equation2 (G : Type*) [Magma G] (h : Equation35810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35811_implies_Equation2 (G : Type*) [Magma G] (h : Equation35811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35812_implies_Equation2 (G : Type*) [Magma G] (h : Equation35812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35814_implies_Equation2 (G : Type*) [Magma G] (h : Equation35814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35815_implies_Equation2 (G : Type*) [Magma G] (h : Equation35815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35816_implies_Equation2 (G : Type*) [Magma G] (h : Equation35816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35817_implies_Equation2 (G : Type*) [Magma G] (h : Equation35817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35819_implies_Equation2 (G : Type*) [Magma G] (h : Equation35819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq10 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) ◇ X3)) ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq14
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) = X2 := superpose eq10 eq14
  have eq33 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose eq14 eq7
  have eq38 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X2) := superpose eq14 eq13
  have eq50 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq13
  have eq52 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq13
  have eq69 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq38
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq50 eq7
  have eq106 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))) := superpose eq50 eq9
  have eq126 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X4)) = ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq13 eq11
  have eq129 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq14 eq11
  have eq171 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq33 eq129
  have eq177 (X0 X1 X3 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X3)) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))))) = X1 := superpose eq171 eq23
  have eq178 (X0 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = X2 := superpose eq171 eq25
  have eq188 (X0 X2 X3 X4 : G) : ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X4)) = ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq171 eq126
  have eq191 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))) := superpose eq171 eq106
  have eq192 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq171 eq101
  have eq232 (X0 X1 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))))) = X1 := superpose eq171 eq177
  have eq233 (X0 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq69 eq178
  have eq246 (X0 X2 X4 : G) : ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X4)) = ((((X2 ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X2 ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq171 eq188
  have eq251 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = (((((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq171 eq191
  have eq252 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq171 eq192
  have eq253 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq69 eq252
  have eq254 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq253 eq52
  have eq258 (X0 X1 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) = X1 := superpose eq253 eq232
  have eq259 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq253 eq233
  have eq264 (X0 X2 X4 : G) : ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X4)) = ((((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq253 eq246
  have eq266 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = ((((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq253 eq251
  have eq273 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq253 eq254
  have eq279 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) = X1 := superpose eq253 eq258
  have eq280 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq253 eq279
  have eq281 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq253 eq280
  have eq282 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq253 eq281
  have eq283 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq253 eq259
  have eq284 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq253 eq283
  have eq301 (X0 X2 X4 : G) : ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X4)) = (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq253 eq264
  have eq302 (X0 X2 X4 : G) : ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X4)) = (((X2 ◇ X2) ◇ X0) ◇ X0) := superpose eq253 eq301
  have eq303 (X0 X2 X4 : G) : (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X4)) = ((X2 ◇ X0) ◇ X0) := superpose eq253 eq302
  have eq304 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X4)) := superpose eq253 eq303
  have eq305 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq273 eq304
  have eq310 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = X2 := superpose eq284 eq266
  have eq311 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = X2 := superpose eq253 eq310
  have eq312 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X2 := superpose eq253 eq311
  have eq313 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq312 eq305
  have eq317 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq313 eq282
  have eq516 (X0 X1 : G) : X0 = X1 := superpose eq313 eq317
  have eq521 (X0 : G) : sK0 ≠ X0 := superpose eq516 eq8
  subsumption eq521 eq516


@[equational_result]
theorem Equation35821_implies_Equation2 (G : Type*) [Magma G] (h : Equation35821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq51 eq21


@[equational_result]
theorem Equation35823_implies_Equation2 (G : Type*) [Magma G] (h : Equation35823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq57 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X4)) ◇ X0) = (((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X5)) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) := superpose eq9 eq10
  have eq72 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X2) = ((X0 ◇ (X0 ◇ X3)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq10 eq26
  have eq87 (X0 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X2) = ((X0 ◇ (X0 ◇ X4)) ◇ X2) := superpose eq7 eq72
  have eq115 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3) = ((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) := superpose eq7 eq87
  have eq127 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0))) := superpose eq9 eq87
  have eq209 (X0 X1 X2 X3 X5 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ X0) = (((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X5)) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) := superpose eq115 eq57
  have eq213 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ X0) = (((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) := superpose eq115 eq209
  have eq220 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) = ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) ◇ X0) := superpose eq127 eq213
  have eq224 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) = X3 := superpose eq220 eq9
  have eq305 (X0 X4 : G) : X0 = X4 := superpose eq224 eq224
  have eq363 (X0 : G) : sK0 ≠ X0 := superpose eq305 eq8
  subsumption eq363 eq305


@[equational_result]
theorem Equation35825_implies_Equation2 (G : Type*) [Magma G] (h : Equation35825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq67 eq21


@[equational_result]
theorem Equation35827_implies_Equation2 (G : Type*) [Magma G] (h : Equation35827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ ((X2 ◇ X3) ◇ X4)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq7 eq10
  have eq41 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq29 eq27
  have eq45 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X3)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X3))) := superpose eq10 eq11
  have eq47 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0))) = X1 := superpose eq10 eq11
  have eq145 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq11 eq41
  have eq146 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := superpose eq7 eq41
  have eq168 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq145 eq11
  have eq197 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq168
  have eq198 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1))) := superpose eq10 eq168
  have eq222 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq146 eq41
  have eq246 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq222 eq197
  have eq253 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq168 eq246
  have eq274 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq253 eq146
  have eq303 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) = X1 := superpose eq274 eq47
  have eq321 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq253 eq303
  have eq322 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X0 := superpose eq321 eq198
  have eq340 (X0 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X2) = (X3 ◇ X3) := superpose eq322 eq45
  have eq435 (X0 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq253 eq340
  have eq436 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq322 eq435
  have eq437 (X0 X3 : G) : X0 = X3 := superpose eq436 eq436
  have eq444 (X0 : G) : sK0 ≠ X0 := superpose eq437 eq8
  subsumption eq444 eq437


@[equational_result]
theorem Equation35829_implies_Equation2 (G : Type*) [Magma G] (h : Equation35829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35831_implies_Equation2 (G : Type*) [Magma G] (h : Equation35831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X5)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X4 ◇ (X4 ◇ X5)) ◇ X0) ◇ X4) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := superpose eq7 eq10
  have eq64 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq7
  have eq76 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) = X0 := superpose eq64 eq7
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X5)) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq64 eq10
  have eq82 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X4 ◇ X5) ◇ X0) ◇ X4) := superpose eq64 eq19
  have eq87 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := superpose eq64 eq29
  have eq101 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((X3 ◇ X4) ◇ (X0 ◇ X5)) := superpose eq64 eq78
  have eq107 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X0 := superpose eq87 eq82
  have eq110 (X0 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X0 ◇ X5)) = X0 := superpose eq107 eq101
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq110 eq76
  have eq117 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X4)) = X0 := superpose eq114 eq87
  have eq122 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq114 eq117
  have eq123 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq114 eq122
  have eq153 (X0 X1 : G) : X0 = X1 := superpose eq114 eq123
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq153 eq8
  subsumption eq166 eq153


@[equational_result]
theorem Equation35832_implies_Equation2 (G : Type*) [Magma G] (h : Equation35832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X0) ◇ (X4 ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)) ◇ X0) ◇ X5) = X2 := superpose eq7 eq11
  have eq23 (X0 X2 X5 : G) : ((X2 ◇ X0) ◇ X5) = X2 := superpose eq11 eq14
  have eq24 (X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5)) ◇ X2) = X4 := superpose eq23 eq9
  have eq27 (X1 X2 X4 : G) : (X1 ◇ X2) = X4 := superpose eq23 eq24
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq27
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation35833_implies_Equation2 (G : Type*) [Magma G] (h : Equation35833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq61 eq18


@[equational_result]
theorem Equation35834_implies_Equation2 (G : Type*) [Magma G] (h : Equation35834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X0) ◇ (X5 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35837_implies_Equation2 (G : Type*) [Magma G] (h : Equation35837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X3) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X4)) ◇ X2) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X2) = X2 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) ◇ X4)) ◇ X2) ◇ X4) = X3 := superpose eq7 eq10
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq11
  have eq43 (X0 X1 X2 X3 X4 : G) : (((((((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X2) ◇ X0) ◇ (((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X2) ◇ X4)) ◇ X4) ◇ X4) ◇ X3) = X3 := superpose eq10 eq16
  have eq67 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose eq34 eq7
  have eq85 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((((((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ (((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ (((((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ (((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X6) ◇ (((((((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ (((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ (((((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ (((((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X7)) ◇ X2) = X7 := superpose eq12 eq12
  have eq292 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X2)) ◇ X1) ◇ X2) := superpose eq34 eq22
  have eq312 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2)) ◇ X1) ◇ X2) := superpose eq34 eq292
  have eq313 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq312
  have eq314 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq313 eq67
  have eq391 (X0 X2 X3 X4 : G) : ((((((X3 ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X4) ◇ X4) ◇ X3) = X3 := superpose eq313 eq43
  have eq467 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((((((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ ((((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X6) ◇ ((((((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ ((((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X0) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X7)) ◇ X2) = X7 := superpose eq313 eq85
  have eq546 (X0 X1 X2 X3 : G) : (((((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ X3) ◇ X1) = X1 := superpose eq313 eq391
  have eq556 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq314 eq314
  have eq558 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq313 eq314
  have eq576 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3)) ◇ X1) = X1 := superpose eq558 eq546
  have eq590 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((((X0 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0))) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ (((X0 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0))) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X6) ◇ (((((X0 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0))) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ (((X0 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0))) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X7)) ◇ X2) = X7 := superpose eq558 eq467
  have eq611 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) = X1 := superpose eq556 eq576
  have eq632 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((((X0 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0))) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X5) ◇ (((X0 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0))) ◇ ((((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0)) ◇ X5)) ◇ X6)) ◇ X6) ◇ X7) ◇ X2) = X7 := superpose eq611 eq590
  have eq633 (X2 X6 X7 : G) : ((X6 ◇ X7) ◇ X2) = X7 := superpose eq611 eq632
  have eq653 (X0 X2 : G) : X0 = X2 := superpose eq313 eq633
  have eq658 (X0 : G) : sK0 ≠ X0 := superpose eq653 eq8
  subsumption eq658 eq653


@[equational_result]
theorem Equation35838_implies_Equation2 (G : Type*) [Magma G] (h : Equation35838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X0) ◇ X5) = X4 := superpose eq7 eq12
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq31 eq20


@[equational_result]
theorem Equation35840_implies_Equation2 (G : Type*) [Magma G] (h : Equation35840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35841_implies_Equation2 (G : Type*) [Magma G] (h : Equation35841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35842_implies_Equation2 (G : Type*) [Magma G] (h : Equation35842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35844_implies_Equation2 (G : Type*) [Magma G] (h : Equation35844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35845_implies_Equation2 (G : Type*) [Magma G] (h : Equation35845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35846_implies_Equation2 (G : Type*) [Magma G] (h : Equation35846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35848_implies_Equation2 (G : Type*) [Magma G] (h : Equation35848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35849_implies_Equation2 (G : Type*) [Magma G] (h : Equation35849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35850_implies_Equation2 (G : Type*) [Magma G] (h : Equation35850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35851_implies_Equation2 (G : Type*) [Magma G] (h : Equation35851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35853_implies_Equation2 (G : Type*) [Magma G] (h : Equation35853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)))) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X4)) ◇ (X4 ◇ X5)))) ◇ X5))) ◇ X0))) ◇ X3) ◇ X1) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq9
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq7
  have eq112 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq50 eq7
  have eq136 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X4) ◇ X5)))) ◇ X5))) ◇ (X4 ◇ (X4 ◇ X0))))) ◇ X3) ◇ X1) = X2 := superpose eq19 eq14
  have eq199 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq112 eq9
  have eq201 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq112 eq7
  have eq229 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq201 eq199
  have eq230 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq229 eq50
  have eq231 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X4)))) ◇ X5))) ◇ (X4 ◇ (X4 ◇ X0))))) ◇ X3) ◇ X1) = X2 := superpose eq230 eq136
  have eq396 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X4)))) ◇ X5))) ◇ (X4 ◇ (X4 ◇ X0))))) ◇ X1) = X2 := superpose eq230 eq231
  have eq397 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq230 eq396
  have eq405 (X0 X1 : G) : X0 = X1 := superpose eq230 eq397
  have eq419 (X0 : G) : sK0 ≠ X0 := superpose eq405 eq8
  subsumption eq419 eq405


@[equational_result]
theorem Equation35854_implies_Equation2 (G : Type*) [Magma G] (h : Equation35854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq41 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq15 eq7
  have eq82 (X0 X2 : G) : X0 = X2 := superpose eq41 eq41
  have eq203 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq203 eq82


@[equational_result]
theorem Equation35855_implies_Equation2 (G : Type*) [Magma G] (h : Equation35855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35857_implies_Equation2 (G : Type*) [Magma G] (h : Equation35857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35858_implies_Equation2 (G : Type*) [Magma G] (h : Equation35858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35859_implies_Equation2 (G : Type*) [Magma G] (h : Equation35859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35861_implies_Equation2 (G : Type*) [Magma G] (h : Equation35861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35862_implies_Equation2 (G : Type*) [Magma G] (h : Equation35862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35863_implies_Equation2 (G : Type*) [Magma G] (h : Equation35863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35865_implies_Equation2 (G : Type*) [Magma G] (h : Equation35865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35866_implies_Equation2 (G : Type*) [Magma G] (h : Equation35866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35867_implies_Equation2 (G : Type*) [Magma G] (h : Equation35867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35868_implies_Equation2 (G : Type*) [Magma G] (h : Equation35868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35870_implies_Equation2 (G : Type*) [Magma G] (h : Equation35870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation35871_implies_Equation2 (G : Type*) [Magma G] (h : Equation35871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation35872_implies_Equation2 (G : Type*) [Magma G] (h : Equation35872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq158 eq60


@[equational_result]
theorem Equation35873_implies_Equation2 (G : Type*) [Magma G] (h : Equation35873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X0) ◇ (X5 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35875_implies_Equation2 (G : Type*) [Magma G] (h : Equation35875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35876_implies_Equation2 (G : Type*) [Magma G] (h : Equation35876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35877_implies_Equation2 (G : Type*) [Magma G] (h : Equation35877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35878_implies_Equation2 (G : Type*) [Magma G] (h : Equation35878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35880_implies_Equation2 (G : Type*) [Magma G] (h : Equation35880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35881_implies_Equation2 (G : Type*) [Magma G] (h : Equation35881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35882_implies_Equation2 (G : Type*) [Magma G] (h : Equation35882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35883_implies_Equation2 (G : Type*) [Magma G] (h : Equation35883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35885_implies_Equation2 (G : Type*) [Magma G] (h : Equation35885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35886_implies_Equation2 (G : Type*) [Magma G] (h : Equation35886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35887_implies_Equation2 (G : Type*) [Magma G] (h : Equation35887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35888_implies_Equation2 (G : Type*) [Magma G] (h : Equation35888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35890_implies_Equation2 (G : Type*) [Magma G] (h : Equation35890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35891_implies_Equation2 (G : Type*) [Magma G] (h : Equation35891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35892_implies_Equation2 (G : Type*) [Magma G] (h : Equation35892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35893_implies_Equation2 (G : Type*) [Magma G] (h : Equation35893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35894_implies_Equation2 (G : Type*) [Magma G] (h : Equation35894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35896_implies_Equation2 (G : Type*) [Magma G] (h : Equation35896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq9 eq9
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq7 eq15
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq61 eq31


@[equational_result]
theorem Equation35897_implies_Equation2 (G : Type*) [Magma G] (h : Equation35897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq11 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq12
  have eq19 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq15 eq12
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq11 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation35898_implies_Equation2 (G : Type*) [Magma G] (h : Equation35898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq12 eq7
  have eq20 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq14
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation35900_implies_Equation2 (G : Type*) [Magma G] (h : Equation35900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((X1 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq48 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq15
  have eq85 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = ((((X2 ◇ X0) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq15 eq9
  have eq86 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X3)) = X4 := superpose eq15 eq9
  have eq99 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))))) ◇ X3))))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))))) ◇ X3)))) = X3 := superpose eq11 eq10
  have eq145 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = X0 := superpose eq15 eq48
  have eq171 (X0 X2 X4 : G) : (X0 ◇ X4) = (X0 ◇ (X2 ◇ X0)) := superpose eq145 eq85
  have eq233 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq171
  have eq434 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq7 eq233
  have eq570 (X1 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ X3) = X3 := superpose eq434 eq99
  have eq589 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq570
  have eq644 (X0 X3 X4 : G) : ((X4 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) = X4 := superpose eq589 eq86
  have eq734 (X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = X4 := superpose eq589 eq644
  have eq735 (X3 X4 : G) : (X3 ◇ X3) = X4 := superpose eq589 eq734
  have eq746 (X0 X1 : G) : X0 = X1 := superpose eq589 eq735
  have eq751 (X0 : G) : sK0 ≠ X0 := superpose eq746 eq8
  subsumption eq751 eq746


@[equational_result]
theorem Equation35902_implies_Equation2 (G : Type*) [Magma G] (h : Equation35902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35904_implies_Equation2 (G : Type*) [Magma G] (h : Equation35904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X3)))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq12
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq12 eq7
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq13 eq10
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X1) = X2 := superpose eq13 eq9
  have eq21 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq13 eq7
  have eq22 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq21 eq21
  have eq42 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq21
  have eq46 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq42
  have eq50 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq42 eq18
  have eq53 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq21 eq50
  have eq56 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X0) = X1 := superpose eq42 eq20
  have eq66 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq42 eq20
  have eq67 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := superpose eq21 eq20
  have eq69 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq42 eq20
  have eq77 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X1 := superpose eq53 eq56
  have eq84 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq46 eq67
  have eq85 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq66 eq69
  have eq89 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq85 eq16
  have eq121 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X1 := superpose eq85 eq77
  have eq150 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq84 eq121
  have eq151 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = X2 := superpose eq150 eq89
  have eq178 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq150 eq151
  have eq186 (X0 X2 : G) : X0 = X2 := superpose eq178 eq178
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq186 eq8
  subsumption eq191 eq186


@[equational_result]
theorem Equation35905_implies_Equation2 (G : Type*) [Magma G] (h : Equation35905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq121 eq36


@[equational_result]
theorem Equation35906_implies_Equation2 (G : Type*) [Magma G] (h : Equation35906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35908_implies_Equation2 (G : Type*) [Magma G] (h : Equation35908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X2 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq7 eq12
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq30 eq12
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq62 eq48


@[equational_result]
theorem Equation35909_implies_Equation2 (G : Type*) [Magma G] (h : Equation35909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X3 ◇ X5)) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35910_implies_Equation2 (G : Type*) [Magma G] (h : Equation35910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq10
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq114 eq33


@[equational_result]
theorem Equation35911_implies_Equation2 (G : Type*) [Magma G] (h : Equation35911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35913_implies_Equation2 (G : Type*) [Magma G] (h : Equation35913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X3 := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq9
  have eq27 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = ((((X0 ◇ (((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X4 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)))) := superpose eq11 eq11
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = (((((((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)))) ◇ X0) ◇ (X5 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2))) ◇ ((((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)))) ◇ X0)) := superpose eq11 eq11
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq11
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := superpose eq13 eq9
  have eq59 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X2 := superpose eq49 eq9
  have eq60 (X0 X1 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X1 ◇ (X1 ◇ X0))) = X3 := superpose eq49 eq13
  have eq61 (X0 X1 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq49 eq15
  have eq70 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = ((((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X4 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq49 eq27
  have eq76 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = ((((((((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) ◇ (X5 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) := superpose eq49 eq30
  have eq86 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq49 eq47
  have eq88 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := superpose eq61 eq70
  have eq89 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := superpose eq49 eq88
  have eq93 (X0 X2 X4 X5 : G) : (((((X0 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) ◇ (X5 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) = X0 := superpose eq89 eq76
  have eq94 (X0 X2 X4 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) = X0 := superpose eq49 eq93
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) := superpose eq49 eq59
  have eq122 (X0 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq118 eq94
  have eq124 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq122 eq86
  have eq130 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) = X3 := superpose eq124 eq60
  have eq159 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = X3 := superpose eq124 eq130
  have eq160 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq124 eq159
  have eq161 (X0 X3 : G) : X0 = X3 := superpose eq160 eq160
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq163 eq161


@[equational_result]
theorem Equation35915_implies_Equation2 (G : Type*) [Magma G] (h : Equation35915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation35917_implies_Equation2 (G : Type*) [Magma G] (h : Equation35917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation35919_implies_Equation2 (G : Type*) [Magma G] (h : Equation35919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation35923_implies_Equation2 (G : Type*) [Magma G] (h : Equation35923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation35925_implies_Equation2 (G : Type*) [Magma G] (h : Equation35925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation35926_implies_Equation2 (G : Type*) [Magma G] (h : Equation35926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X4))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X1 ◇ X4)) ◇ X5)) ◇ X2) = X3 := superpose eq7 eq7
  have eq40 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq9 eq10
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq151 eq52


@[equational_result]
theorem Equation35927_implies_Equation2 (G : Type*) [Magma G] (h : Equation35927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X0) ◇ X3) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ X0) ◇ X3) = X5 := superpose eq12 eq11
  have eq16 (X0 X3 X5 : G) : ((X5 ◇ X0) ◇ X3) = X5 := superpose eq12 eq13
  have eq17 (X1 X4 X5 : G) : (X1 ◇ X5) = X4 := superpose eq16 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation35928_implies_Equation2 (G : Type*) [Magma G] (h : Equation35928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation35930_implies_Equation2 (G : Type*) [Magma G] (h : Equation35930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq38 eq18


@[equational_result]
theorem Equation35931_implies_Equation2 (G : Type*) [Magma G] (h : Equation35931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq89 eq30


@[equational_result]
theorem Equation35932_implies_Equation2 (G : Type*) [Magma G] (h : Equation35932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq9 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation35936_implies_Equation2 (G : Type*) [Magma G] (h : Equation35936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation35939_implies_Equation2 (G : Type*) [Magma G] (h : Equation35939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation35940_implies_Equation2 (G : Type*) [Magma G] (h : Equation35940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation35942_implies_Equation2 (G : Type*) [Magma G] (h : Equation35942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq66 eq21


@[equational_result]
theorem Equation35943_implies_Equation2 (G : Type*) [Magma G] (h : Equation35943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X2 ◇ X5)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq59 eq18


@[equational_result]
theorem Equation35944_implies_Equation2 (G : Type*) [Magma G] (h : Equation35944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation35945_implies_Equation2 (G : Type*) [Magma G] (h : Equation35945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation35947_implies_Equation2 (G : Type*) [Magma G] (h : Equation35947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq61 eq32


@[equational_result]
theorem Equation35948_implies_Equation2 (G : Type*) [Magma G] (h : Equation35948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X5 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation35949_implies_Equation2 (G : Type*) [Magma G] (h : Equation35949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X4 ◇ (X5 ◇ X0)) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ (X5 ◇ X0))) = X3 := superpose eq12 eq11
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = X3 := superpose eq12 eq13
  have eq18 (X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X4) = X3 := superpose eq12 eq17
  have eq19 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation35950_implies_Equation2 (G : Type*) [Magma G] (h : Equation35950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 X6 X7 : G) : (((X1 ◇ X0) ◇ (X6 ◇ X5)) ◇ X7) = X5 := superpose eq7 eq7
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X6 ◇ X5)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X5 X7 : G) : ((X1 ◇ X0) ◇ X7) = X5 := superpose eq13 eq9
  have eq16 (X1 X5 X7 : G) : (X1 ◇ X7) = X5 := superpose eq13 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation35952_implies_Equation2 (G : Type*) [Magma G] (h : Equation35952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation35953_implies_Equation2 (G : Type*) [Magma G] (h : Equation35953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq140 eq45


@[equational_result]
theorem Equation35954_implies_Equation2 (G : Type*) [Magma G] (h : Equation35954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation35955_implies_Equation2 (G : Type*) [Magma G] (h : Equation35955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation35957_implies_Equation2 (G : Type*) [Magma G] (h : Equation35957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq125 eq38


@[equational_result]
theorem Equation35958_implies_Equation2 (G : Type*) [Magma G] (h : Equation35958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X5 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation35959_implies_Equation2 (G : Type*) [Magma G] (h : Equation35959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X5 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation35960_implies_Equation2 (G : Type*) [Magma G] (h : Equation35960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35962_implies_Equation2 (G : Type*) [Magma G] (h : Equation35962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation35963_implies_Equation2 (G : Type*) [Magma G] (h : Equation35963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X5)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X4))) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X5)) ◇ (X4 ◇ X4)) = X3 := superpose eq11 eq9
  have eq15 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X5)) ◇ X4) = X3 := superpose eq11 eq12
  have eq16 (X3 X4 X5 : G) : ((X5 ◇ X5) ◇ X4) = X3 := superpose eq11 eq15
  have eq17 (X3 X4 X5 : G) : (X5 ◇ X4) = X3 := superpose eq11 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation35964_implies_Equation2 (G : Type*) [Magma G] (h : Equation35964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ (X5 ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq46 eq29


@[equational_result]
theorem Equation35965_implies_Equation2 (G : Type*) [Magma G] (h : Equation35965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35967_implies_Equation2 (G : Type*) [Magma G] (h : Equation35967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (((X1 ◇ X0) ◇ (X6 ◇ X7)) ◇ X1) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation35968_implies_Equation2 (G : Type*) [Magma G] (h : Equation35968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35969_implies_Equation2 (G : Type*) [Magma G] (h : Equation35969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35970_implies_Equation2 (G : Type*) [Magma G] (h : Equation35970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X7) = X5 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation35971_implies_Equation2 (G : Type*) [Magma G] (h : Equation35971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation35973_implies_Equation2 (G : Type*) [Magma G] (h : Equation35973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq9 eq9
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq7 eq14
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq62 eq28


@[equational_result]
theorem Equation35975_implies_Equation2 (G : Type*) [Magma G] (h : Equation35975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation35977_implies_Equation2 (G : Type*) [Magma G] (h : Equation35977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ X1)) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X0)) = ((((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq10 eq7
  have eq39 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ (X4 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ (X0 ◇ (X3 ◇ X0))) = X4 := superpose eq10 eq9
  have eq47 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq32 eq30
  have eq58 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0)) = X0 := superpose eq10 eq32
  have eq72 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq58 eq38
  have eq76 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X3 ◇ X1)) := superpose eq7 eq72
  have eq128 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ X2) := superpose eq7 eq76
  have eq220 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq47 eq128
  have eq309 (X0 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X0))) = X4 := superpose eq220 eq39
  have eq334 (X0 X4 : G) : X0 = X4 := superpose eq7 eq309
  have eq418 (X0 : G) : sK0 ≠ X0 := superpose eq334 eq8
  subsumption eq418 eq334


@[equational_result]
theorem Equation35979_implies_Equation2 (G : Type*) [Magma G] (h : Equation35979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ (X4 ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq9
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq155 eq42


@[equational_result]
theorem Equation35983_implies_Equation2 (G : Type*) [Magma G] (h : Equation35983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35985_implies_Equation2 (G : Type*) [Magma G] (h : Equation35985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation35986_implies_Equation2 (G : Type*) [Magma G] (h : Equation35986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq53 eq12


@[equational_result]
theorem Equation35987_implies_Equation2 (G : Type*) [Magma G] (h : Equation35987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35988_implies_Equation2 (G : Type*) [Magma G] (h : Equation35988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35990_implies_Equation2 (G : Type*) [Magma G] (h : Equation35990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X3 := superpose eq9 eq9
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X2)) := superpose eq12 eq9
  have eq53 (X1 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X1) = X3 := superpose eq45 eq9
  have eq93 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq53 eq45
  have eq122 (X0 X3 : G) : X0 = X3 := superpose eq93 eq93
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq164 eq122


@[equational_result]
theorem Equation35992_implies_Equation2 (G : Type*) [Magma G] (h : Equation35992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X0) ◇ X5) = X4 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation35994_implies_Equation2 (G : Type*) [Magma G] (h : Equation35994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35995_implies_Equation2 (G : Type*) [Magma G] (h : Equation35995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35996_implies_Equation2 (G : Type*) [Magma G] (h : Equation35996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35998_implies_Equation2 (G : Type*) [Magma G] (h : Equation35998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35999_implies_Equation2 (G : Type*) [Magma G] (h : Equation35999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36000_implies_Equation2 (G : Type*) [Magma G] (h : Equation36000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36002_implies_Equation2 (G : Type*) [Magma G] (h : Equation36002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36003_implies_Equation2 (G : Type*) [Magma G] (h : Equation36003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36004_implies_Equation2 (G : Type*) [Magma G] (h : Equation36004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36005_implies_Equation2 (G : Type*) [Magma G] (h : Equation36005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36008_implies_Equation2 (G : Type*) [Magma G] (h : Equation36008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X3)) = (((X1 ◇ (((X2 ◇ X3) ◇ (((X4 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X3)) ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X2 ◇ X3) ◇ (((X4 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X3)) ◇ X0))) := superpose eq9 eq7
  have eq41 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq11 eq9
  have eq42 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X2) ◇ X2)) = X3 := superpose eq11 eq7
  have eq44 (X0 X1 X3 X4 : G) : ((X0 ◇ (((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)) ◇ X0) ◇ X4)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)) ◇ X0)) = X4 := superpose eq11 eq9
  have eq51 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq11 eq41
  have eq52 (X0 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X2) ◇ X2)) = X3 := superpose eq7 eq42
  have eq163 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq52
  have eq183 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = ((((((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)))) ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) := superpose eq51 eq16
  have eq230 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq163
  have eq264 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = ((((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) := superpose eq230 eq183
  have eq316 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq230 eq230
  have eq352 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = ((((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq316 eq264
  have eq365 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = X3 := superpose eq230 eq352
  have eq366 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq365 eq7
  have eq411 (X0 X1 X3 X4 : G) : ((X0 ◇ (((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) ◇ X4)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0)) = X4 := superpose eq366 eq44
  have eq452 (X0 X1 X3 X4 : G) : ((X0 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4)) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = X4 := superpose eq366 eq411
  have eq453 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X3) = X4 := superpose eq366 eq452
  have eq454 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq366 eq453
  have eq455 (X0 X3 : G) : X0 = X3 := superpose eq454 eq454
  have eq460 (X0 : G) : sK0 ≠ X0 := superpose eq455 eq8
  subsumption eq460 eq455


@[equational_result]
theorem Equation36009_implies_Equation2 (G : Type*) [Magma G] (h : Equation36009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36011_implies_Equation2 (G : Type*) [Magma G] (h : Equation36011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36012_implies_Equation2 (G : Type*) [Magma G] (h : Equation36012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36013_implies_Equation2 (G : Type*) [Magma G] (h : Equation36013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36015_implies_Equation2 (G : Type*) [Magma G] (h : Equation36015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36016_implies_Equation2 (G : Type*) [Magma G] (h : Equation36016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36017_implies_Equation2 (G : Type*) [Magma G] (h : Equation36017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36019_implies_Equation2 (G : Type*) [Magma G] (h : Equation36019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36020_implies_Equation2 (G : Type*) [Magma G] (h : Equation36020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36021_implies_Equation2 (G : Type*) [Magma G] (h : Equation36021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36022_implies_Equation2 (G : Type*) [Magma G] (h : Equation36022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36024_implies_Equation2 (G : Type*) [Magma G] (h : Equation36024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation36025_implies_Equation2 (G : Type*) [Magma G] (h : Equation36025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation36026_implies_Equation2 (G : Type*) [Magma G] (h : Equation36026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation36027_implies_Equation2 (G : Type*) [Magma G] (h : Equation36027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36029_implies_Equation2 (G : Type*) [Magma G] (h : Equation36029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36030_implies_Equation2 (G : Type*) [Magma G] (h : Equation36030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36031_implies_Equation2 (G : Type*) [Magma G] (h : Equation36031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36032_implies_Equation2 (G : Type*) [Magma G] (h : Equation36032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36034_implies_Equation2 (G : Type*) [Magma G] (h : Equation36034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36035_implies_Equation2 (G : Type*) [Magma G] (h : Equation36035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36036_implies_Equation2 (G : Type*) [Magma G] (h : Equation36036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36037_implies_Equation2 (G : Type*) [Magma G] (h : Equation36037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36039_implies_Equation2 (G : Type*) [Magma G] (h : Equation36039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36040_implies_Equation2 (G : Type*) [Magma G] (h : Equation36040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36041_implies_Equation2 (G : Type*) [Magma G] (h : Equation36041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36042_implies_Equation2 (G : Type*) [Magma G] (h : Equation36042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36044_implies_Equation2 (G : Type*) [Magma G] (h : Equation36044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36045_implies_Equation2 (G : Type*) [Magma G] (h : Equation36045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36046_implies_Equation2 (G : Type*) [Magma G] (h : Equation36046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36047_implies_Equation2 (G : Type*) [Magma G] (h : Equation36047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36048_implies_Equation2 (G : Type*) [Magma G] (h : Equation36048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36050_implies_Equation2 (G : Type*) [Magma G] (h : Equation36050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation36051_implies_Equation2 (G : Type*) [Magma G] (h : Equation36051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation36052_implies_Equation2 (G : Type*) [Magma G] (h : Equation36052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36056_implies_Equation2 (G : Type*) [Magma G] (h : Equation36056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36059_implies_Equation2 (G : Type*) [Magma G] (h : Equation36059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq151 eq51


@[equational_result]
theorem Equation36060_implies_Equation2 (G : Type*) [Magma G] (h : Equation36060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36062_implies_Equation2 (G : Type*) [Magma G] (h : Equation36062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation36063_implies_Equation2 (G : Type*) [Magma G] (h : Equation36063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36064_implies_Equation2 (G : Type*) [Magma G] (h : Equation36064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq11 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq11
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation36065_implies_Equation2 (G : Type*) [Magma G] (h : Equation36065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36067_implies_Equation2 (G : Type*) [Magma G] (h : Equation36067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3)) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq7 eq10
  have eq21 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := superpose eq9 eq9
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq9 eq7
  have eq34 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq11 eq10
  have eq37 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) := superpose eq11 eq9
  have eq40 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq11 eq9
  have eq41 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2))) := superpose eq11 eq10
  have eq47 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq34 eq40
  have eq52 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose eq23 eq9
  have eq55 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = ((((((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose eq23 eq10
  have eq57 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq47
  have eq70 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq57 eq21
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq57 eq41
  have eq77 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq57 eq47
  have eq81 (X0 X1 : G) : (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq57 eq70
  have eq82 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq57 eq81
  have eq110 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq77 eq82
  have eq117 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq57 eq110
  have eq118 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq117 eq57
  have eq121 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) := superpose eq118 eq37
  have eq130 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq118 eq7
  have eq143 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq118 eq52
  have eq144 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = ((((((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose eq118 eq55
  have eq147 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq118 eq74
  have eq165 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq118 eq121
  have eq166 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) := superpose eq118 eq165
  have eq167 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq118 eq166
  have eq168 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = ((X0 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq118 eq167
  have eq219 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq168 eq143
  have eq220 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq118 eq219
  have eq221 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = ((((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq118 eq144
  have eq222 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (((((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq118 eq221
  have eq223 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq168 eq222
  have eq224 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq118 eq223
  have eq228 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq118 eq147
  have eq229 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq118 eq228
  have eq230 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq229 eq224
  have eq231 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq230 eq220
  have eq233 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq118 eq231
  have eq234 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X0 := superpose eq233 eq130
  have eq260 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq233 eq234
  have eq261 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq233 eq260
  have eq268 (X0 X2 : G) : X0 = X2 := superpose eq261 eq261
  have eq270 (X0 : G) : sK0 ≠ X0 := superpose eq268 eq8
  subsumption eq270 eq268


@[equational_result]
theorem Equation36068_implies_Equation2 (G : Type*) [Magma G] (h : Equation36068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq10 eq10
  have eq22 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq16 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq43 eq31


@[equational_result]
theorem Equation36069_implies_Equation2 (G : Type*) [Magma G] (h : Equation36069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation36071_implies_Equation2 (G : Type*) [Magma G] (h : Equation36071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36072_implies_Equation2 (G : Type*) [Magma G] (h : Equation36072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36073_implies_Equation2 (G : Type*) [Magma G] (h : Equation36073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36075_implies_Equation2 (G : Type*) [Magma G] (h : Equation36075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36076_implies_Equation2 (G : Type*) [Magma G] (h : Equation36076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36077_implies_Equation2 (G : Type*) [Magma G] (h : Equation36077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36079_implies_Equation2 (G : Type*) [Magma G] (h : Equation36079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36080_implies_Equation2 (G : Type*) [Magma G] (h : Equation36080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36081_implies_Equation2 (G : Type*) [Magma G] (h : Equation36081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36082_implies_Equation2 (G : Type*) [Magma G] (h : Equation36082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36085_implies_Equation2 (G : Type*) [Magma G] (h : Equation36085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq98 eq31


@[equational_result]
theorem Equation36086_implies_Equation2 (G : Type*) [Magma G] (h : Equation36086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36088_implies_Equation2 (G : Type*) [Magma G] (h : Equation36088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36089_implies_Equation2 (G : Type*) [Magma G] (h : Equation36089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36090_implies_Equation2 (G : Type*) [Magma G] (h : Equation36090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36092_implies_Equation2 (G : Type*) [Magma G] (h : Equation36092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36093_implies_Equation2 (G : Type*) [Magma G] (h : Equation36093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36094_implies_Equation2 (G : Type*) [Magma G] (h : Equation36094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36096_implies_Equation2 (G : Type*) [Magma G] (h : Equation36096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36097_implies_Equation2 (G : Type*) [Magma G] (h : Equation36097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36098_implies_Equation2 (G : Type*) [Magma G] (h : Equation36098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36099_implies_Equation2 (G : Type*) [Magma G] (h : Equation36099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36101_implies_Equation2 (G : Type*) [Magma G] (h : Equation36101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation36102_implies_Equation2 (G : Type*) [Magma G] (h : Equation36102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36103_implies_Equation2 (G : Type*) [Magma G] (h : Equation36103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq9
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq11 eq26
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq54 eq31


@[equational_result]
theorem Equation36104_implies_Equation2 (G : Type*) [Magma G] (h : Equation36104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36106_implies_Equation2 (G : Type*) [Magma G] (h : Equation36106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36107_implies_Equation2 (G : Type*) [Magma G] (h : Equation36107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36108_implies_Equation2 (G : Type*) [Magma G] (h : Equation36108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36109_implies_Equation2 (G : Type*) [Magma G] (h : Equation36109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36111_implies_Equation2 (G : Type*) [Magma G] (h : Equation36111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36112_implies_Equation2 (G : Type*) [Magma G] (h : Equation36112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36113_implies_Equation2 (G : Type*) [Magma G] (h : Equation36113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36114_implies_Equation2 (G : Type*) [Magma G] (h : Equation36114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36116_implies_Equation2 (G : Type*) [Magma G] (h : Equation36116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36117_implies_Equation2 (G : Type*) [Magma G] (h : Equation36117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36118_implies_Equation2 (G : Type*) [Magma G] (h : Equation36118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36119_implies_Equation2 (G : Type*) [Magma G] (h : Equation36119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36121_implies_Equation2 (G : Type*) [Magma G] (h : Equation36121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36122_implies_Equation2 (G : Type*) [Magma G] (h : Equation36122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36123_implies_Equation2 (G : Type*) [Magma G] (h : Equation36123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36124_implies_Equation2 (G : Type*) [Magma G] (h : Equation36124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36125_implies_Equation2 (G : Type*) [Magma G] (h : Equation36125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36127_implies_Equation2 (G : Type*) [Magma G] (h : Equation36127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq26 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq37 eq26


@[equational_result]
theorem Equation36128_implies_Equation2 (G : Type*) [Magma G] (h : Equation36128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation36129_implies_Equation2 (G : Type*) [Magma G] (h : Equation36129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation36130_implies_Equation2 (G : Type*) [Magma G] (h : Equation36130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36132_implies_Equation2 (G : Type*) [Magma G] (h : Equation36132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X4 ◇ X5)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq42 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ ((X3 ◇ X0) ◇ X0)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X0) := superpose eq11 eq11
  have eq44 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq11
  have eq61 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq44 eq42
  have eq70 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq44 eq44
  have eq238 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq61
  have eq270 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq238 eq70
  have eq274 (X0 X4 : G) : X0 = X4 := superpose eq7 eq270
  have eq489 (X0 : G) : sK0 ≠ X0 := superpose eq274 eq8
  subsumption eq489 eq274


@[equational_result]
theorem Equation36133_implies_Equation2 (G : Type*) [Magma G] (h : Equation36133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X1)) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X5 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X1)))) ◇ X2) = X5 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X6 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ (X3 ◇ (X4 ◇ X5))) = X6 := superpose eq9 eq7
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ (X1 ◇ X2)))) ◇ (X6 ◇ ((X3 ◇ ((X7 ◇ X8) ◇ X9)) ◇ X0))) ◇ X7) = X6 := superpose eq10 eq10
  have eq57 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq25 eq39
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq57
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq193 eq58


@[equational_result]
theorem Equation36134_implies_Equation2 (G : Type*) [Magma G] (h : Equation36134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X1)) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq9 eq9
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq168 eq46


@[equational_result]
theorem Equation36135_implies_Equation2 (G : Type*) [Magma G] (h : Equation36135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36137_implies_Equation2 (G : Type*) [Magma G] (h : Equation36137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq151 eq51


@[equational_result]
theorem Equation36138_implies_Equation2 (G : Type*) [Magma G] (h : Equation36138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq36 eq13


@[equational_result]
theorem Equation36139_implies_Equation2 (G : Type*) [Magma G] (h : Equation36139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X5 ◇ X3)) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36140_implies_Equation2 (G : Type*) [Magma G] (h : Equation36140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : ((X0 ◇ (X6 ◇ X4)) ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36142_implies_Equation2 (G : Type*) [Magma G] (h : Equation36142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq44 eq32


@[equational_result]
theorem Equation36143_implies_Equation2 (G : Type*) [Magma G] (h : Equation36143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X5 ◇ X3)) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36144_implies_Equation2 (G : Type*) [Magma G] (h : Equation36144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ (X5 ◇ X4)) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq10
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq138 eq33


@[equational_result]
theorem Equation36145_implies_Equation2 (G : Type*) [Magma G] (h : Equation36145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X6 ◇ X5)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36147_implies_Equation2 (G : Type*) [Magma G] (h : Equation36147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq43 eq32


@[equational_result]
theorem Equation36148_implies_Equation2 (G : Type*) [Magma G] (h : Equation36148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X6 X7 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X2) = X6 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36149_implies_Equation2 (G : Type*) [Magma G] (h : Equation36149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36150_implies_Equation2 (G : Type*) [Magma G] (h : Equation36150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36151_implies_Equation2 (G : Type*) [Magma G] (h : Equation36151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X7 X8 X9 : G) : ((X0 ◇ (X7 ◇ X8)) ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X2 X5 : G) : (X2 ◇ X5) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36153_implies_Equation2 (G : Type*) [Magma G] (h : Equation36153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = X1 := superpose eq7 eq11
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq7 eq24
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq101 eq50


@[equational_result]
theorem Equation36154_implies_Equation2 (G : Type*) [Magma G] (h : Equation36154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X0))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X1 ◇ X0)) ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X8 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ X8)) ◇ X3) = X8 := superpose eq10 eq10
  have eq34 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X1 ◇ ((X0 ◇ (((X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X6)) ◇ (X2 ◇ X0)) ◇ X1)) ◇ X7)) ◇ X3) = X7 := superpose eq7 eq10
  have eq56 (X1 X3 X7 : G) : ((X1 ◇ X1) ◇ X3) = X7 := superpose eq33 eq34
  have eq83 (X0 X5 : G) : X0 = X5 := superpose eq9 eq56
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq160 eq83


@[equational_result]
theorem Equation36155_implies_Equation2 (G : Type*) [Magma G] (h : Equation36155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X0)) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : ((X0 ◇ X0) ◇ X4) = X5 := superpose eq9 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation36156_implies_Equation2 (G : Type*) [Magma G] (h : Equation36156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation36158_implies_Equation2 (G : Type*) [Magma G] (h : Equation36158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36159_implies_Equation2 (G : Type*) [Magma G] (h : Equation36159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36160_implies_Equation2 (G : Type*) [Magma G] (h : Equation36160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36161_implies_Equation2 (G : Type*) [Magma G] (h : Equation36161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36163_implies_Equation2 (G : Type*) [Magma G] (h : Equation36163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36164_implies_Equation2 (G : Type*) [Magma G] (h : Equation36164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36165_implies_Equation2 (G : Type*) [Magma G] (h : Equation36165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36166_implies_Equation2 (G : Type*) [Magma G] (h : Equation36166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36168_implies_Equation2 (G : Type*) [Magma G] (h : Equation36168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36169_implies_Equation2 (G : Type*) [Magma G] (h : Equation36169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36170_implies_Equation2 (G : Type*) [Magma G] (h : Equation36170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36171_implies_Equation2 (G : Type*) [Magma G] (h : Equation36171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36173_implies_Equation2 (G : Type*) [Magma G] (h : Equation36173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36174_implies_Equation2 (G : Type*) [Magma G] (h : Equation36174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36175_implies_Equation2 (G : Type*) [Magma G] (h : Equation36175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36176_implies_Equation2 (G : Type*) [Magma G] (h : Equation36176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36177_implies_Equation2 (G : Type*) [Magma G] (h : Equation36177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36179_implies_Equation2 (G : Type*) [Magma G] (h : Equation36179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation36180_implies_Equation2 (G : Type*) [Magma G] (h : Equation36180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : ((X0 ◇ (X2 ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq10
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq123 eq38


@[equational_result]
theorem Equation36181_implies_Equation2 (G : Type*) [Magma G] (h : Equation36181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36182_implies_Equation2 (G : Type*) [Magma G] (h : Equation36182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : ((X0 ◇ (X4 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36184_implies_Equation2 (G : Type*) [Magma G] (h : Equation36184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36185_implies_Equation2 (G : Type*) [Magma G] (h : Equation36185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36186_implies_Equation2 (G : Type*) [Magma G] (h : Equation36186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36187_implies_Equation2 (G : Type*) [Magma G] (h : Equation36187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36189_implies_Equation2 (G : Type*) [Magma G] (h : Equation36189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36190_implies_Equation2 (G : Type*) [Magma G] (h : Equation36190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36191_implies_Equation2 (G : Type*) [Magma G] (h : Equation36191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36192_implies_Equation2 (G : Type*) [Magma G] (h : Equation36192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36194_implies_Equation2 (G : Type*) [Magma G] (h : Equation36194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36195_implies_Equation2 (G : Type*) [Magma G] (h : Equation36195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36196_implies_Equation2 (G : Type*) [Magma G] (h : Equation36196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36197_implies_Equation2 (G : Type*) [Magma G] (h : Equation36197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36199_implies_Equation2 (G : Type*) [Magma G] (h : Equation36199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36200_implies_Equation2 (G : Type*) [Magma G] (h : Equation36200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36201_implies_Equation2 (G : Type*) [Magma G] (h : Equation36201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36202_implies_Equation2 (G : Type*) [Magma G] (h : Equation36202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36203_implies_Equation2 (G : Type*) [Magma G] (h : Equation36203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36205_implies_Equation2 (G : Type*) [Magma G] (h : Equation36205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq106 eq40


@[equational_result]
theorem Equation36206_implies_Equation2 (G : Type*) [Magma G] (h : Equation36206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : ((X0 ◇ (X3 ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36207_implies_Equation2 (G : Type*) [Magma G] (h : Equation36207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq37 eq13


@[equational_result]
theorem Equation36208_implies_Equation2 (G : Type*) [Magma G] (h : Equation36208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36210_implies_Equation2 (G : Type*) [Magma G] (h : Equation36210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36211_implies_Equation2 (G : Type*) [Magma G] (h : Equation36211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36212_implies_Equation2 (G : Type*) [Magma G] (h : Equation36212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36213_implies_Equation2 (G : Type*) [Magma G] (h : Equation36213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36215_implies_Equation2 (G : Type*) [Magma G] (h : Equation36215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36216_implies_Equation2 (G : Type*) [Magma G] (h : Equation36216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36217_implies_Equation2 (G : Type*) [Magma G] (h : Equation36217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36218_implies_Equation2 (G : Type*) [Magma G] (h : Equation36218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36220_implies_Equation2 (G : Type*) [Magma G] (h : Equation36220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36221_implies_Equation2 (G : Type*) [Magma G] (h : Equation36221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36222_implies_Equation2 (G : Type*) [Magma G] (h : Equation36222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36223_implies_Equation2 (G : Type*) [Magma G] (h : Equation36223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36225_implies_Equation2 (G : Type*) [Magma G] (h : Equation36225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36226_implies_Equation2 (G : Type*) [Magma G] (h : Equation36226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36227_implies_Equation2 (G : Type*) [Magma G] (h : Equation36227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36228_implies_Equation2 (G : Type*) [Magma G] (h : Equation36228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36229_implies_Equation2 (G : Type*) [Magma G] (h : Equation36229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36231_implies_Equation2 (G : Type*) [Magma G] (h : Equation36231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation36232_implies_Equation2 (G : Type*) [Magma G] (h : Equation36232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X6 X7 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X2) = X7 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36233_implies_Equation2 (G : Type*) [Magma G] (h : Equation36233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X4) = X7 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36234_implies_Equation2 (G : Type*) [Magma G] (h : Equation36234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36235_implies_Equation2 (G : Type*) [Magma G] (h : Equation36235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X7 X8 X9 : G) : ((X0 ◇ (X7 ◇ X8)) ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X3 ◇ X5) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36237_implies_Equation2 (G : Type*) [Magma G] (h : Equation36237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36238_implies_Equation2 (G : Type*) [Magma G] (h : Equation36238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36239_implies_Equation2 (G : Type*) [Magma G] (h : Equation36239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36240_implies_Equation2 (G : Type*) [Magma G] (h : Equation36240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36241_implies_Equation2 (G : Type*) [Magma G] (h : Equation36241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36243_implies_Equation2 (G : Type*) [Magma G] (h : Equation36243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36244_implies_Equation2 (G : Type*) [Magma G] (h : Equation36244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36245_implies_Equation2 (G : Type*) [Magma G] (h : Equation36245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36246_implies_Equation2 (G : Type*) [Magma G] (h : Equation36246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36247_implies_Equation2 (G : Type*) [Magma G] (h : Equation36247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36249_implies_Equation2 (G : Type*) [Magma G] (h : Equation36249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36250_implies_Equation2 (G : Type*) [Magma G] (h : Equation36250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36251_implies_Equation2 (G : Type*) [Magma G] (h : Equation36251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36252_implies_Equation2 (G : Type*) [Magma G] (h : Equation36252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36253_implies_Equation2 (G : Type*) [Magma G] (h : Equation36253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36255_implies_Equation2 (G : Type*) [Magma G] (h : Equation36255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36256_implies_Equation2 (G : Type*) [Magma G] (h : Equation36256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36257_implies_Equation2 (G : Type*) [Magma G] (h : Equation36257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36258_implies_Equation2 (G : Type*) [Magma G] (h : Equation36258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36259_implies_Equation2 (G : Type*) [Magma G] (h : Equation36259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36261_implies_Equation2 (G : Type*) [Magma G] (h : Equation36261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36262_implies_Equation2 (G : Type*) [Magma G] (h : Equation36262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36263_implies_Equation2 (G : Type*) [Magma G] (h : Equation36263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36264_implies_Equation2 (G : Type*) [Magma G] (h : Equation36264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36265_implies_Equation2 (G : Type*) [Magma G] (h : Equation36265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36266_implies_Equation2 (G : Type*) [Magma G] (h : Equation36266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36472_implies_Equation2 (G : Type*) [Magma G] (h : Equation36472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq7 eq9
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq16 eq10
  have eq22 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq21
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq22 eq7
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq22 eq35
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq22 eq44
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation36475_implies_Equation2 (G : Type*) [Magma G] (h : Equation36475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))))) ◇ X3) = X0 := superpose eq7 eq10
  have eq25 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq12
  have eq27 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3) = X2 := superpose eq25 eq9
  have eq34 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq25 eq27
  have eq35 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq25 eq34
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq35 eq35
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation36477_implies_Equation2 (G : Type*) [Magma G] (h : Equation36477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) = ((((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X3))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = ((((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ X1) := superpose eq9 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq9 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq10 eq10
  have eq113 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = ((((X4 ◇ (X0 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X1) ◇ X4) := superpose eq7 eq22
  have eq170 (X0 X1 X4 : G) : ((((X4 ◇ X0) ◇ X0) ◇ X1) ◇ X4) = X0 := superpose eq7 eq113
  have eq183 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X4))) := superpose eq113 eq9
  have eq208 (X0 X1 X2 X3 : G) : ((((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((((((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq11 eq25
  have eq255 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq10 eq170
  have eq263 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq7 eq170
  have eq270 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq170 eq170
  have eq317 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq263 eq255
  have eq326 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq317 eq29
  have eq389 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq326 eq170
  have eq425 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (X1 ◇ X3)) := superpose eq389 eq208
  have eq481 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = (((X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X4))) := superpose eq389 eq183
  have eq524 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X1) ◇ (X1 ◇ X3)) := superpose eq389 eq425
  have eq567 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = (((X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X4))) := superpose eq389 eq481
  have eq568 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X4))) := superpose eq270 eq567
  have eq569 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq389 eq568
  have eq570 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X3)) := superpose eq569 eq524
  have eq588 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq270
  have eq646 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ X1) := superpose eq588 eq570
  have eq844 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose eq588 eq646
  have eq845 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ X1) := superpose eq588 eq844
  have eq846 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq588 eq845
  have eq847 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X1 := superpose eq588 eq846
  have eq848 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq588 eq847
  have eq849 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq588 eq848
  have eq1207 (X0 X2 : G) : X0 = X2 := superpose eq849 eq849
  have eq1209 (X0 : G) : sK0 ≠ X0 := superpose eq1207 eq8
  subsumption eq1209 eq1207


@[equational_result]
theorem Equation36478_implies_Equation2 (G : Type*) [Magma G] (h : Equation36478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq9
  have eq38 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq11
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq7 eq38
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq183 eq71


@[equational_result]
theorem Equation36479_implies_Equation2 (G : Type*) [Magma G] (h : Equation36479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X5 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = (X0 ◇ X5) := superpose eq7 eq10
  have eq42 (X0 X5 : G) : (X0 ◇ X5) = X0 := superpose eq7 eq31
  have eq45 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq42 eq7
  have eq53 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq42 eq45
  have eq54 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq42 eq53
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq54 eq54
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq57 eq55


@[equational_result]
theorem Equation36482_implies_Equation2 (G : Type*) [Magma G] (h : Equation36482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq10 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq101 eq32


@[equational_result]
theorem Equation36485_implies_Equation2 (G : Type*) [Magma G] (h : Equation36485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq12
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq15 eq7
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq15 eq20
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq15 eq24
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation36489_implies_Equation2 (G : Type*) [Magma G] (h : Equation36489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq15
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq18 eq12
  have eq20 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq19 eq18
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq20 eq19
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation36491_implies_Equation2 (G : Type*) [Magma G] (h : Equation36491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11
  have eq32 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X0)) = ((((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X0))) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X0)))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq9 eq9
  have eq45 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1))))) = X1 := superpose eq16 eq35
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq16
  have eq63 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X0)) = (((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X0)))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq49 eq32
  have eq65 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) = X1 := superpose eq49 eq45
  have eq87 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X0)) = (((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)))) := superpose eq49 eq63
  have eq88 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X0)) = (((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq49 eq87
  have eq89 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = ((X1 ◇ X0) ◇ (X3 ◇ X0)) := superpose eq49 eq88
  have eq90 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq49 eq89
  have eq91 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq49 eq90
  have eq92 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq49 eq91
  have eq93 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq49 eq92
  have eq94 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq49 eq93
  have eq97 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq49 eq65
  have eq98 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = X1 := superpose eq49 eq97
  have eq99 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq49 eq98
  have eq100 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq49 eq99
  have eq101 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq49 eq100
  have eq102 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq49 eq101
  have eq165 (X0 X1 : G) : X0 = X1 := superpose eq94 eq102
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq170 eq165


@[equational_result]
theorem Equation36492_implies_Equation2 (G : Type*) [Magma G] (h : Equation36492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq9
  have eq35 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq11
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq189 eq77


@[equational_result]
theorem Equation36493_implies_Equation2 (G : Type*) [Magma G] (h : Equation36493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq14 eq7
  have eq23 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq21 eq9
  have eq27 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq21 eq23
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq33 eq28


@[equational_result]
theorem Equation36495_implies_Equation2 (G : Type*) [Magma G] (h : Equation36495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq10
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq15 eq14
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq19 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq23 eq15
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq31 eq23
  have eq44 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq31 eq39
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq44 eq44
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation36497_implies_Equation2 (G : Type*) [Magma G] (h : Equation36497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X4 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X4 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X5) = X3 := superpose eq12 eq9
  have eq17 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq12 eq13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq17 eq12
  have eq19 (X3 X5 : G) : (X3 ◇ X5) = X3 := superpose eq18 eq17
  have eq25 (X0 X1 : G) : X0 = X1 := superpose eq18 eq19
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation36500_implies_Equation2 (G : Type*) [Magma G] (h : Equation36500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq10
  have eq18 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X2) ◇ (X2 ◇ X2)) := superpose eq7 eq9
  have eq23 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq11 eq18
  have eq24 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = X0 := superpose eq23 eq7
  have eq30 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq23 eq24
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq39 eq37


@[equational_result]
theorem Equation36501_implies_Equation2 (G : Type*) [Magma G] (h : Equation36501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq12
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq13 eq7
  have eq23 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq13 eq18
  have eq24 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation36503_implies_Equation2 (G : Type*) [Magma G] (h : Equation36503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq12
  have eq39 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq29 eq7
  have eq50 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq29 eq39
  have eq59 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq50 eq50
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq59 eq18
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq80 eq64


@[equational_result]
theorem Equation36504_implies_Equation2 (G : Type*) [Magma G] (h : Equation36504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X2) ◇ (X4 ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ X0) ◇ (X4 ◇ X5))) = X2 := superpose eq7 eq9
  have eq25 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq11
  have eq38 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq25
  have eq51 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ X0)) = X2 := superpose eq38 eq14
  have eq69 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) = X2 := superpose eq38 eq51
  have eq70 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq38 eq69
  have eq71 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq38 eq70
  have eq72 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq38 eq71
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq72 eq72
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq75 eq73


@[equational_result]
theorem Equation36505_implies_Equation2 (G : Type*) [Magma G] (h : Equation36505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X4 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq14 eq7
  have eq23 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq21 eq9
  have eq27 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq21 eq23
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq33 eq28


@[equational_result]
theorem Equation36506_implies_Equation2 (G : Type*) [Magma G] (h : Equation36506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = X0 := superpose eq12 eq7
  have eq16 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X0 := superpose eq12 eq13
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq16 eq12
  have eq19 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq17 eq16
  have eq23 (X0 X1 : G) : X0 = X1 := superpose eq19 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation36509_implies_Equation2 (G : Type*) [Magma G] (h : Equation36509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq12 eq9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq12 eq14
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq21
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation36512_implies_Equation2 (G : Type*) [Magma G] (h : Equation36512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X3) = X2 := superpose eq12 eq9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq12 eq14
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq21
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation36516_implies_Equation2 (G : Type*) [Magma G] (h : Equation36516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq12 eq9
  have eq21 (X0 X1 X3 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X5) = X3 := superpose eq12 eq14
  have eq22 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq21
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation36519_implies_Equation2 (G : Type*) [Magma G] (h : Equation36519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation36522_implies_Equation2 (G : Type*) [Magma G] (h : Equation36522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq13
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq12 eq15
  have eq19 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation36526_implies_Equation2 (G : Type*) [Magma G] (h : Equation36526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq64 eq15


@[equational_result]
theorem Equation36528_implies_Equation2 (G : Type*) [Magma G] (h : Equation36528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq13 eq10
  have eq77 (X0 X2 : G) : X0 = X2 := superpose eq13 eq42
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq103 eq77


@[equational_result]
theorem Equation36529_implies_Equation2 (G : Type*) [Magma G] (h : Equation36529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (((X3 ◇ X0) ◇ X3) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X1)) ◇ X2) = X1 := superpose eq11 eq7
  have eq52 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq42
  have eq104 (X0 X3 : G) : X0 = X3 := superpose eq7 eq52
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq227 eq104


@[equational_result]
theorem Equation36530_implies_Equation2 (G : Type*) [Magma G] (h : Equation36530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation36532_implies_Equation2 (G : Type*) [Magma G] (h : Equation36532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq35 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq13 eq10
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) := superpose eq7 eq14
  have eq54 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq36 eq7
  have eq63 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq54 eq35
  have eq74 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq63 eq54
  have eq110 (X0 X2 : G) : X0 = X2 := superpose eq74 eq74
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq110 eq8
  subsumption eq112 eq110


@[equational_result]
theorem Equation36534_implies_Equation2 (G : Type*) [Magma G] (h : Equation36534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) ◇ (X4 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X5) = X3 := superpose eq12 eq9
  have eq17 (X0 X1 X3 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X5) = X3 := superpose eq12 eq13
  have eq18 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq17
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation36538_implies_Equation2 (G : Type*) [Magma G] (h : Equation36538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X4 ◇ X4)) ◇ X5) = X3 := superpose eq12 eq9
  have eq17 (X0 X1 X3 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X5) = X3 := superpose eq12 eq13
  have eq18 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq17
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation36540_implies_Equation2 (G : Type*) [Magma G] (h : Equation36540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) := superpose eq7 eq11
  have eq32 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq22 eq7
  have eq37 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X2 := superpose eq32 eq10
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq32 eq37
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq47 eq44


@[equational_result]
theorem Equation36541_implies_Equation2 (G : Type*) [Magma G] (h : Equation36541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ X2) := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq7 eq12
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq177 eq73


@[equational_result]
theorem Equation36542_implies_Equation2 (G : Type*) [Magma G] (h : Equation36542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation36543_implies_Equation2 (G : Type*) [Magma G] (h : Equation36543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36545_implies_Equation2 (G : Type*) [Magma G] (h : Equation36545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X1) = X2 := superpose eq11 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq11
  have eq30 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq27
  have eq34 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq30 eq7
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq30 eq14
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq38 eq34
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq53 eq51


@[equational_result]
theorem Equation36546_implies_Equation2 (G : Type*) [Magma G] (h : Equation36546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq9
  have eq13 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq10 eq18
  have eq27 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq26 eq10
  have eq28 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq27
  have eq30 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq28 eq13
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq55 eq35


@[equational_result]
theorem Equation36547_implies_Equation2 (G : Type*) [Magma G] (h : Equation36547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36549_implies_Equation2 (G : Type*) [Magma G] (h : Equation36549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = ((((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq10 eq9
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq24
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq24 eq10
  have eq53 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq24 eq7
  have eq68 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X1))) = (((((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X1)))) ◇ X5) ◇ X0) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X1)) := superpose eq11 eq11
  have eq76 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ (X0 ◇ X1)) = ((((((X1 ◇ X0) ◇ X2) ◇ (((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ (X0 ◇ X1))) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq10 eq11
  have eq80 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = ((((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) ◇ X0) := superpose eq24 eq11
  have eq98 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq80
  have eq116 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq98 eq7
  have eq133 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X0))) = X0 := superpose eq98 eq47
  have eq136 (X0 X1 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X4) ◇ (X0 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3) ◇ X1))) = (((((((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X4) ◇ (X0 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3) ◇ X1)))) ◇ X5) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3) ◇ X1)) := superpose eq98 eq68
  have eq149 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose eq98 eq133
  have eq168 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq116 eq116
  have eq174 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq168 eq10
  have eq178 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq53 eq53
  have eq191 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq178 eq52
  have eq201 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq178 eq174
  have eq214 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq149 eq201
  have eq227 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq214 eq116
  have eq244 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1))) = (((((((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1) ◇ (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1)))) ◇ X5) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1)) := superpose eq214 eq136
  have eq264 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq214 eq191
  have eq294 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq227 eq264
  have eq295 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1))) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1) ◇ (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1)))) ◇ X5) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1)) := superpose eq294 eq244
  have eq301 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ X1)) = ((((((X1 ◇ X0) ◇ X2) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ X1))) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq294 eq76
  have eq356 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) = (((((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)))) ◇ X5) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq294 eq295
  have eq357 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X5) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq294 eq356
  have eq358 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ X0)) = (((X0 ◇ (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ X0))) ◇ X5) ◇ X0) := superpose eq294 eq357
  have eq359 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ X0)) = ((X0 ◇ (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq294 eq358
  have eq360 (X0 X1 X4 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X4) ◇ (X0 ◇ X0)) := superpose eq294 eq359
  have eq361 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X0) = X0 := superpose eq214 eq360
  have eq362 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq294 eq361
  have eq363 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq294 eq362
  have eq376 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq363 eq301
  have eq377 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ X1) := superpose eq363 eq376
  have eq378 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq294 eq377
  have eq379 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq294 eq378
  have eq380 (X0 X1 : G) : X0 = X1 := superpose eq214 eq379
  have eq388 (X0 : G) : sK0 ≠ X0 := superpose eq380 eq8
  subsumption eq388 eq380


@[equational_result]
theorem Equation36551_implies_Equation2 (G : Type*) [Magma G] (h : Equation36551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation36554_implies_Equation2 (G : Type*) [Magma G] (h : Equation36554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq9
  have eq32 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq12
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq138 eq70


@[equational_result]
theorem Equation36555_implies_Equation2 (G : Type*) [Magma G] (h : Equation36555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36557_implies_Equation2 (G : Type*) [Magma G] (h : Equation36557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq12
  have eq20 (X0 X1 X2 X4 : G) : ((X0 ◇ (X2 ◇ X4)) ◇ X1) = X2 := superpose eq12 eq7
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq15 eq12
  have eq40 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq25 eq20
  have eq41 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq40 eq14
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq54 eq49


@[equational_result]
theorem Equation36558_implies_Equation2 (G : Type*) [Magma G] (h : Equation36558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X2 ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X4 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X5) := superpose eq10 eq10
  have eq38 (X0 X1 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X5) := superpose eq12 eq28
  have eq40 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq38 eq7
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq38 eq40
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq46 eq38
  have eq48 (X0 X2 X4 X5 : G) : ((X0 ◇ X5) ◇ X2) = X4 := superpose eq47 eq12
  have eq51 (X2 X4 X5 : G) : (X5 ◇ X2) = X4 := superpose eq47 eq48
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq71 eq60


@[equational_result]
theorem Equation36559_implies_Equation2 (G : Type*) [Magma G] (h : Equation36559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36560_implies_Equation2 (G : Type*) [Magma G] (h : Equation36560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36562_implies_Equation2 (G : Type*) [Magma G] (h : Equation36562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))))) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq17
  have eq50 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq31 eq13
  have eq51 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq31 eq24
  have eq67 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X0 := superpose eq31 eq51
  have eq68 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq31 eq67
  have eq69 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq68 eq50
  have eq71 (X0 X1 : G) : X0 = X1 := superpose eq68 eq69
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq73 eq71


@[equational_result]
theorem Equation36563_implies_Equation2 (G : Type*) [Magma G] (h : Equation36563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq42 eq15


@[equational_result]
theorem Equation36564_implies_Equation2 (G : Type*) [Magma G] (h : Equation36564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation36566_implies_Equation2 (G : Type*) [Magma G] (h : Equation36566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq27 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq9
  have eq41 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq27 eq10
  have eq43 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq27 eq13
  have eq71 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose eq7 eq27
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq27 eq27
  have eq75 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq27 eq7
  have eq79 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq72 eq41
  have eq90 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ X3)) := superpose eq7 eq79
  have eq92 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq79 eq79
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq79 eq79
  have eq99 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) = X1 := superpose eq79 eq7
  have eq106 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq27 eq92
  have eq107 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X3)) = X1 := superpose eq27 eq106
  have eq109 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq96 eq43
  have eq110 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X3)) = X1 := superpose eq109 eq107
  have eq116 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X3)) := superpose eq110 eq90
  have eq120 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq116 eq99
  have eq121 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq71 eq120
  have eq122 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq121 eq109
  have eq124 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq122 eq75
  have eq156 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq122 eq124
  have eq157 (X0 X3 : G) : X0 = X3 := superpose eq156 eq156
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq162 eq157


@[equational_result]
theorem Equation36568_implies_Equation2 (G : Type*) [Magma G] (h : Equation36568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation36572_implies_Equation2 (G : Type*) [Magma G] (h : Equation36572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation36574_implies_Equation2 (G : Type*) [Magma G] (h : Equation36574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X5)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X5)) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4)) ◇ X1) = X2 := superpose eq10 eq7
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq10 eq9
  have eq77 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X5)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X2 := superpose eq53 eq27
  have eq142 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq53 eq77
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq142 eq142
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq151 eq143


@[equational_result]
theorem Equation36575_implies_Equation2 (G : Type*) [Magma G] (h : Equation36575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X5) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X5) = (X4 ◇ X0) := superpose eq7 eq12
  have eq35 (X0 X4 X5 : G) : (((X4 ◇ X0) ◇ X0) ◇ X5) = X4 := superpose eq19 eq11
  have eq44 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq35
  have eq60 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X4) = X2 := superpose eq44 eq9
  have eq84 (X2 X4 X5 : G) : (X5 ◇ X4) = X2 := superpose eq44 eq60
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq84 eq84
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq87 eq85


@[equational_result]
theorem Equation36576_implies_Equation2 (G : Type*) [Magma G] (h : Equation36576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation36577_implies_Equation2 (G : Type*) [Magma G] (h : Equation36577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation36580_implies_Equation2 (G : Type*) [Magma G] (h : Equation36580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq9
  have eq31 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq12
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq173 eq70


@[equational_result]
theorem Equation36581_implies_Equation2 (G : Type*) [Magma G] (h : Equation36581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36585_implies_Equation2 (G : Type*) [Magma G] (h : Equation36585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation36588_implies_Equation2 (G : Type*) [Magma G] (h : Equation36588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation36589_implies_Equation2 (G : Type*) [Magma G] (h : Equation36589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36591_implies_Equation2 (G : Type*) [Magma G] (h : Equation36591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq12 eq7
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq164 eq62


@[equational_result]
theorem Equation36592_implies_Equation2 (G : Type*) [Magma G] (h : Equation36592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X4 ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation36593_implies_Equation2 (G : Type*) [Magma G] (h : Equation36593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation36594_implies_Equation2 (G : Type*) [Magma G] (h : Equation36594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36596_implies_Equation2 (G : Type*) [Magma G] (h : Equation36596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq12 eq11
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq105 eq35


@[equational_result]
theorem Equation36597_implies_Equation2 (G : Type*) [Magma G] (h : Equation36597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X2)) ◇ X4) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation36598_implies_Equation2 (G : Type*) [Magma G] (h : Equation36598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36599_implies_Equation2 (G : Type*) [Magma G] (h : Equation36599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36601_implies_Equation2 (G : Type*) [Magma G] (h : Equation36601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq11
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq146 eq61


@[equational_result]
theorem Equation36602_implies_Equation2 (G : Type*) [Magma G] (h : Equation36602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq160 eq57


@[equational_result]
theorem Equation36603_implies_Equation2 (G : Type*) [Magma G] (h : Equation36603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation36604_implies_Equation2 (G : Type*) [Magma G] (h : Equation36604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36606_implies_Equation2 (G : Type*) [Magma G] (h : Equation36606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq135 eq38


@[equational_result]
theorem Equation36607_implies_Equation2 (G : Type*) [Magma G] (h : Equation36607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X4)) ◇ X4) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation36608_implies_Equation2 (G : Type*) [Magma G] (h : Equation36608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation36609_implies_Equation2 (G : Type*) [Magma G] (h : Equation36609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36611_implies_Equation2 (G : Type*) [Magma G] (h : Equation36611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation36612_implies_Equation2 (G : Type*) [Magma G] (h : Equation36612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq58 eq41


@[equational_result]
theorem Equation36613_implies_Equation2 (G : Type*) [Magma G] (h : Equation36613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation36614_implies_Equation2 (G : Type*) [Magma G] (h : Equation36614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36616_implies_Equation2 (G : Type*) [Magma G] (h : Equation36616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation36617_implies_Equation2 (G : Type*) [Magma G] (h : Equation36617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ (X6 ◇ X7)) ◇ X5) = X2 := superpose eq7 eq7
  have eq47 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq68 eq47


@[equational_result]
theorem Equation36618_implies_Equation2 (G : Type*) [Magma G] (h : Equation36618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36619_implies_Equation2 (G : Type*) [Magma G] (h : Equation36619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36620_implies_Equation2 (G : Type*) [Magma G] (h : Equation36620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X7 : G) : (X0 ◇ X7) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation36623_implies_Equation2 (G : Type*) [Magma G] (h : Equation36623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X1 := superpose eq7 eq7
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq9 eq10
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq108 eq39


@[equational_result]
theorem Equation36626_implies_Equation2 (G : Type*) [Magma G] (h : Equation36626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq16
  have eq22 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq21
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq22 eq7
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq22 eq11
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq26
  have eq33 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq32 eq23
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq32 eq33
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq36
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation36628_implies_Equation2 (G : Type*) [Magma G] (h : Equation36628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = ((((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = ((((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ X1) := superpose eq9 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) = (((X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq10
  have eq19 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X3) := superpose eq9 eq10
  have eq23 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) = ((((X3 ◇ X3) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X3) := superpose eq9 eq10
  have eq28 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq10
  have eq32 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq9 eq28
  have eq33 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq9 eq32
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq32
  have eq129 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0)) ◇ ((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0)))) = X2 := superpose eq17 eq16
  have eq137 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq35 eq35
  have eq141 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq35 eq35
  have eq152 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq35 eq9
  have eq153 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq35 eq33
  have eq164 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq7
  have eq203 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq152 eq141
  have eq269 (X0 X1 X2 X3 X4 : G) : (((((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (((((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ ((((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X4)) := superpose eq19 eq137
  have eq396 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) = X2 := superpose eq269 eq129
  have eq557 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq153 eq18
  have eq562 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq153 eq16
  have eq587 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq557
  have eq595 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) ◇ X3) = (((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) ◇ (X0 ◇ X0)) := superpose eq35 eq23
  have eq905 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) := superpose eq203 eq587
  have eq1034 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) := superpose eq153 eq905
  have eq1035 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq1034 eq562
  have eq1036 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq9 eq1035
  have eq1051 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) = X2 := superpose eq1036 eq164
  have eq1057 (X0 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) ◇ X3) = ((X0 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) ◇ (X0 ◇ X0)) := superpose eq1036 eq595
  have eq1062 (X0 X1 X2 : G) : (X0 ◇ (((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) = X2 := superpose eq1036 eq396
  have eq1118 (X2 X3 X4 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) ◇ X3) := superpose eq1051 eq1057
  have eq1168 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) = X2 := superpose eq1118 eq1062
  have eq1169 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq203 eq1168
  have eq1380 (X0 X1 : G) : X0 = X1 := superpose eq9 eq1169
  have eq1579 (X0 : G) : sK0 ≠ X0 := superpose eq1380 eq8
  subsumption eq1579 eq1380


@[equational_result]
theorem Equation36630_implies_Equation2 (G : Type*) [Magma G] (h : Equation36630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq7 eq7
  have eq34 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq9 eq10
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq123 eq43


@[equational_result]
theorem Equation36633_implies_Equation2 (G : Type*) [Magma G] (h : Equation36633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq12
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq108 eq40


@[equational_result]
theorem Equation36636_implies_Equation2 (G : Type*) [Magma G] (h : Equation36636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) = X0 := superpose eq10 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq10 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36639_implies_Equation2 (G : Type*) [Magma G] (h : Equation36639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq10 eq10
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq10 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((((((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0) ◇ ((((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0)) ◇ X4) ◇ X3) ◇ X2) = X4 := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)))) ◇ X3) = ((((((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)))) ◇ X3) ◇ X1) ◇ X2) := superpose eq10 eq9
  have eq35 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq11
  have eq46 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) = (((((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) ◇ X1) ◇ X2) := superpose eq35 eq19
  have eq53 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) = X3 := superpose eq9 eq46
  have eq55 (X0 X2 X3 X4 : G) : (((((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ X4) ◇ X3) ◇ X2) = X4 := superpose eq53 eq15
  have eq56 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X3 := superpose eq53 eq9
  have eq58 (X0 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ X2) = X4 := superpose eq56 eq55
  have eq72 (X2 X3 X4 : G) : (X3 ◇ X2) = X4 := superpose eq56 eq58
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq72 eq72
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq81 eq73


@[equational_result]
theorem Equation36640_implies_Equation2 (G : Type*) [Magma G] (h : Equation36640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ X4) = X0 := superpose eq7 eq11
  have eq29 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq7 eq14
  have eq30 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X3) = X0 := superpose eq29 eq7
  have eq33 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq29 eq30
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq29 eq33
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation36642_implies_Equation2 (G : Type*) [Magma G] (h : Equation36642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq10
  have eq77 (X0 X1 : G) : X0 = X1 := superpose eq9 eq14
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq112 eq77


@[equational_result]
theorem Equation36643_implies_Equation2 (G : Type*) [Magma G] (h : Equation36643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ X3) := superpose eq7 eq9
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq13
  have eq142 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq142 eq8
  subsumption eq153 eq142


@[equational_result]
theorem Equation36644_implies_Equation2 (G : Type*) [Magma G] (h : Equation36644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq97 eq36


@[equational_result]
theorem Equation36646_implies_Equation2 (G : Type*) [Magma G] (h : Equation36646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq10
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq62 eq24


@[equational_result]
theorem Equation36648_implies_Equation2 (G : Type*) [Magma G] (h : Equation36648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq31 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq11
  have eq53 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq31 eq7
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq68 eq59


@[equational_result]
theorem Equation36650_implies_Equation2 (G : Type*) [Magma G] (h : Equation36650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq10
  have eq52 (X0 X1 : G) : X0 = X1 := superpose eq9 eq28
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq126 eq52


@[equational_result]
theorem Equation36651_implies_Equation2 (G : Type*) [Magma G] (h : Equation36651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := superpose eq9 eq7
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq14 eq9
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = X0 := superpose eq20 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq20 eq10
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq20 eq21
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq20 eq22
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq20 eq27
  have eq29 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq28 eq26
  have eq30 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq28 eq29
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation36652_implies_Equation2 (G : Type*) [Magma G] (h : Equation36652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X4 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq36 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq9
  have eq53 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq36 eq7
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq9 eq53
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq118 eq55


@[equational_result]
theorem Equation36654_implies_Equation2 (G : Type*) [Magma G] (h : Equation36654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X1) := superpose eq9 eq7
  have eq36 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq29
  have eq128 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq128 eq8
  subsumption eq235 eq128


@[equational_result]
theorem Equation36655_implies_Equation2 (G : Type*) [Magma G] (h : Equation36655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ (X2 ◇ X3)) ◇ X2) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq67 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq163 eq67


@[equational_result]
theorem Equation36656_implies_Equation2 (G : Type*) [Magma G] (h : Equation36656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X3) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X1 := superpose eq7 eq9
  have eq21 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq12 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq36 eq28


@[equational_result]
theorem Equation36657_implies_Equation2 (G : Type*) [Magma G] (h : Equation36657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation36660_implies_Equation2 (G : Type*) [Magma G] (h : Equation36660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) ◇ X4) = X3 := superpose eq7 eq9
  have eq21 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X4) = X3 := superpose eq7 eq13
  have eq34 (X0 X1 X2 X3 X5 : G) : (((X3 ◇ X3) ◇ X3) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X5) := superpose eq10 eq10
  have eq35 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq10
  have eq51 (X0 X1 X2 X5 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X5) = X1 := superpose eq35 eq34
  have eq98 (X0 X2 : G) : X0 = X2 := superpose eq21 eq51
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq121 eq98


@[equational_result]
theorem Equation36663_implies_Equation2 (G : Type*) [Magma G] (h : Equation36663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X2) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq48 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)))) ◇ X4) = X3 := superpose eq11 eq10
  have eq64 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq7 eq48
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq7 eq64
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq161 eq65


@[equational_result]
theorem Equation36665_implies_Equation2 (G : Type*) [Magma G] (h : Equation36665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) = ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = ((((X4 ◇ X4) ◇ X4) ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X3))) ◇ X4) := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X4) := superpose eq17 eq11
  have eq113 (X0 X4 X5 : G) : ((X4 ◇ X4) ◇ X5) = X0 := superpose eq17 eq26
  have eq178 (X0 X3 : G) : X0 = X3 := superpose eq113 eq113
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq271 eq178


@[equational_result]
theorem Equation36666_implies_Equation2 (G : Type*) [Magma G] (h : Equation36666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) = ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X1))) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) ◇ (X3 ◇ X4)) ◇ X4) = X3 := superpose eq9 eq7
  have eq35 (X1 X3 X4 : G) : ((X1 ◇ (X3 ◇ X4)) ◇ X4) = X3 := superpose eq7 eq27
  have eq40 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq35
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq40
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq124 eq52


@[equational_result]
theorem Equation36667_implies_Equation2 (G : Type*) [Magma G] (h : Equation36667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq10
  have eq22 (X1 X3 X5 : G) : (((X1 ◇ X1) ◇ X1) ◇ X5) = X3 := superpose eq12 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq22
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq48 eq30


@[equational_result]
theorem Equation36670_implies_Equation2 (G : Type*) [Magma G] (h : Equation36670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq37 eq26


@[equational_result]
theorem Equation36672_implies_Equation2 (G : Type*) [Magma G] (h : Equation36672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation36673_implies_Equation2 (G : Type*) [Magma G] (h : Equation36673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36675_implies_Equation2 (G : Type*) [Magma G] (h : Equation36675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36676_implies_Equation2 (G : Type*) [Magma G] (h : Equation36676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36677_implies_Equation2 (G : Type*) [Magma G] (h : Equation36677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36679_implies_Equation2 (G : Type*) [Magma G] (h : Equation36679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq23 eq13


@[equational_result]
theorem Equation36680_implies_Equation2 (G : Type*) [Magma G] (h : Equation36680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X4) ◇ X4) ◇ (X2 ◇ X0)) = ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ X0)) := superpose eq7 eq9
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ X5) ◇ X5) ◇ X3) = ((((X1 ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X4 ◇ X4) ◇ X4) ◇ X0)) := superpose eq9 eq9
  have eq27 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq10
  have eq53 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq27 eq27
  have eq157 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) = X1 := superpose eq10 eq53
  have eq159 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ (((X4 ◇ X4) ◇ X4) ◇ X0)) := superpose eq53 eq11
  have eq179 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq157 eq159
  have eq180 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq179 eq7
  have eq273 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq180 eq27
  have eq277 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq180 eq179
  have eq280 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq277 eq273
  have eq285 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq277 eq280
  have eq286 (X0 X3 : G) : X0 = X3 := superpose eq285 eq285
  have eq288 (X0 : G) : sK0 ≠ X0 := superpose eq286 eq8
  subsumption eq288 eq286


@[equational_result]
theorem Equation36681_implies_Equation2 (G : Type*) [Magma G] (h : Equation36681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X4 X5 : G) : ((X2 ◇ X0) ◇ X5) = X4 := superpose eq10 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation36683_implies_Equation2 (G : Type*) [Magma G] (h : Equation36683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36684_implies_Equation2 (G : Type*) [Magma G] (h : Equation36684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36685_implies_Equation2 (G : Type*) [Magma G] (h : Equation36685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36687_implies_Equation2 (G : Type*) [Magma G] (h : Equation36687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36688_implies_Equation2 (G : Type*) [Magma G] (h : Equation36688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36689_implies_Equation2 (G : Type*) [Magma G] (h : Equation36689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36691_implies_Equation2 (G : Type*) [Magma G] (h : Equation36691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36692_implies_Equation2 (G : Type*) [Magma G] (h : Equation36692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36693_implies_Equation2 (G : Type*) [Magma G] (h : Equation36693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36694_implies_Equation2 (G : Type*) [Magma G] (h : Equation36694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36696_implies_Equation2 (G : Type*) [Magma G] (h : Equation36696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq35 eq13


@[equational_result]
theorem Equation36697_implies_Equation2 (G : Type*) [Magma G] (h : Equation36697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq30 eq12


@[equational_result]
theorem Equation36698_implies_Equation2 (G : Type*) [Magma G] (h : Equation36698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36700_implies_Equation2 (G : Type*) [Magma G] (h : Equation36700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq9 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq13 eq10
  have eq21 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq17 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq32 eq29


@[equational_result]
theorem Equation36702_implies_Equation2 (G : Type*) [Magma G] (h : Equation36702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation36704_implies_Equation2 (G : Type*) [Magma G] (h : Equation36704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq69 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq43
  have eq70 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq69 eq7
  have eq113 (X0 X2 : G) : X0 = X2 := superpose eq9 eq70
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq113 eq8
  subsumption eq126 eq113


@[equational_result]
theorem Equation36705_implies_Equation2 (G : Type*) [Magma G] (h : Equation36705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X2) ◇ (X0 ◇ X2)) = ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq7 eq9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq9 eq9
  have eq37 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq7 eq10
  have eq82 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq14 eq37
  have eq84 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq82 eq11
  have eq107 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq82 eq84
  have eq110 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X2 := superpose eq107 eq9
  have eq118 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq107 eq110
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq118 eq118
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq121 eq119


@[equational_result]
theorem Equation36706_implies_Equation2 (G : Type*) [Magma G] (h : Equation36706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36708_implies_Equation2 (G : Type*) [Magma G] (h : Equation36708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq40 eq15


@[equational_result]
theorem Equation36709_implies_Equation2 (G : Type*) [Magma G] (h : Equation36709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation36710_implies_Equation2 (G : Type*) [Magma G] (h : Equation36710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation36711_implies_Equation2 (G : Type*) [Magma G] (h : Equation36711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation36715_implies_Equation2 (G : Type*) [Magma G] (h : Equation36715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq53 eq14


@[equational_result]
theorem Equation36717_implies_Equation2 (G : Type*) [Magma G] (h : Equation36717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation36718_implies_Equation2 (G : Type*) [Magma G] (h : Equation36718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation36719_implies_Equation2 (G : Type*) [Magma G] (h : Equation36719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36721_implies_Equation2 (G : Type*) [Magma G] (h : Equation36721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36722_implies_Equation2 (G : Type*) [Magma G] (h : Equation36722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36723_implies_Equation2 (G : Type*) [Magma G] (h : Equation36723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36725_implies_Equation2 (G : Type*) [Magma G] (h : Equation36725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36726_implies_Equation2 (G : Type*) [Magma G] (h : Equation36726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36727_implies_Equation2 (G : Type*) [Magma G] (h : Equation36727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36728_implies_Equation2 (G : Type*) [Magma G] (h : Equation36728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36732_implies_Equation2 (G : Type*) [Magma G] (h : Equation36732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation36734_implies_Equation2 (G : Type*) [Magma G] (h : Equation36734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36735_implies_Equation2 (G : Type*) [Magma G] (h : Equation36735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36736_implies_Equation2 (G : Type*) [Magma G] (h : Equation36736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36738_implies_Equation2 (G : Type*) [Magma G] (h : Equation36738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36739_implies_Equation2 (G : Type*) [Magma G] (h : Equation36739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36740_implies_Equation2 (G : Type*) [Magma G] (h : Equation36740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36742_implies_Equation2 (G : Type*) [Magma G] (h : Equation36742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36743_implies_Equation2 (G : Type*) [Magma G] (h : Equation36743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36744_implies_Equation2 (G : Type*) [Magma G] (h : Equation36744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36745_implies_Equation2 (G : Type*) [Magma G] (h : Equation36745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36747_implies_Equation2 (G : Type*) [Magma G] (h : Equation36747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation36748_implies_Equation2 (G : Type*) [Magma G] (h : Equation36748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq38 eq15


@[equational_result]
theorem Equation36749_implies_Equation2 (G : Type*) [Magma G] (h : Equation36749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq39 eq12


@[equational_result]
theorem Equation36750_implies_Equation2 (G : Type*) [Magma G] (h : Equation36750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36752_implies_Equation2 (G : Type*) [Magma G] (h : Equation36752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36753_implies_Equation2 (G : Type*) [Magma G] (h : Equation36753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36754_implies_Equation2 (G : Type*) [Magma G] (h : Equation36754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36755_implies_Equation2 (G : Type*) [Magma G] (h : Equation36755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36757_implies_Equation2 (G : Type*) [Magma G] (h : Equation36757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36758_implies_Equation2 (G : Type*) [Magma G] (h : Equation36758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36759_implies_Equation2 (G : Type*) [Magma G] (h : Equation36759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36760_implies_Equation2 (G : Type*) [Magma G] (h : Equation36760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36762_implies_Equation2 (G : Type*) [Magma G] (h : Equation36762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36763_implies_Equation2 (G : Type*) [Magma G] (h : Equation36763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36764_implies_Equation2 (G : Type*) [Magma G] (h : Equation36764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36765_implies_Equation2 (G : Type*) [Magma G] (h : Equation36765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36767_implies_Equation2 (G : Type*) [Magma G] (h : Equation36767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36768_implies_Equation2 (G : Type*) [Magma G] (h : Equation36768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36769_implies_Equation2 (G : Type*) [Magma G] (h : Equation36769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36770_implies_Equation2 (G : Type*) [Magma G] (h : Equation36770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36771_implies_Equation2 (G : Type*) [Magma G] (h : Equation36771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36773_implies_Equation2 (G : Type*) [Magma G] (h : Equation36773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) := superpose eq7 eq10
  have eq20 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X0))) = X3 := superpose eq10 eq7
  have eq41 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq20
  have eq119 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ X2) := superpose eq7 eq41
  have eq150 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq119 eq17
  have eq157 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) := superpose eq150 eq150
  have eq231 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq41 eq157
  have eq234 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq231 eq7
  have eq244 (X0 X1 : G) : X0 = X1 := superpose eq20 eq234
  have eq337 (X0 : G) : sK0 ≠ X0 := superpose eq244 eq8
  subsumption eq337 eq244


@[equational_result]
theorem Equation36774_implies_Equation2 (G : Type*) [Magma G] (h : Equation36774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq10
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq9 eq21
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq9 eq32
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq93 eq35


@[equational_result]
theorem Equation36775_implies_Equation2 (G : Type*) [Magma G] (h : Equation36775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X4) = X3 := superpose eq7 eq7
  have eq28 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq101 eq42


@[equational_result]
theorem Equation36777_implies_Equation2 (G : Type*) [Magma G] (h : Equation36777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)))) ◇ (((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3))) = X1 := superpose eq7 eq9
  have eq77 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq9 eq11
  have eq154 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X2 := superpose eq77 eq9
  have eq155 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq77 eq7
  have eq175 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)))) = X1 := superpose eq7 eq155
  have eq192 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq155 eq7
  have eq194 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq155 eq10
  have eq446 (X0 X1 : G) : (X0 ◇ X1) = ((((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq192 eq194
  have eq453 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq154 eq446
  have eq602 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7 eq453
  have eq660 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq602 eq175
  have eq668 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq453 eq660
  have eq687 (X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) = X2 := superpose eq668 eq154
  have eq802 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq668 eq687
  have eq812 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))))) ◇ (((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)))) = X1 := superpose eq802 eq19
  have eq1093 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))))) ◇ ((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)))) = X1 := superpose eq802 eq812
  have eq1094 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X4)) = X1 := superpose eq802 eq1093
  have eq1095 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X3) = X1 := superpose eq802 eq1094
  have eq1096 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq802 eq1095
  have eq1097 (X0 X3 : G) : X0 = X3 := superpose eq1096 eq1096
  have eq1099 (X0 : G) : sK0 ≠ X0 := superpose eq1097 eq8
  subsumption eq1099 eq1097


@[equational_result]
theorem Equation36779_implies_Equation2 (G : Type*) [Magma G] (h : Equation36779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4) = X3 := superpose eq7 eq7
  have eq41 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq10
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq148 eq54


@[equational_result]
theorem Equation36782_implies_Equation2 (G : Type*) [Magma G] (h : Equation36782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq9
  have eq31 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq12
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq179 eq73


@[equational_result]
theorem Equation36783_implies_Equation2 (G : Type*) [Magma G] (h : Equation36783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ X3) := superpose eq7 eq7
  have eq39 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X1 := superpose eq12 eq9
  have eq52 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq39 eq7
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq9 eq52
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq100 eq55


@[equational_result]
theorem Equation36785_implies_Equation2 (G : Type*) [Magma G] (h : Equation36785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X4)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X3 : G) : (X0 ◇ X3) = (X0 ◇ X1) := superpose eq10 eq7
  have eq42 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X4) = X0 := superpose eq10 eq21
  have eq150 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq7 eq42
  have eq237 (X0 X4 : G) : X0 = X4 := superpose eq7 eq150
  have eq433 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq433 eq237


@[equational_result]
theorem Equation36786_implies_Equation2 (G : Type*) [Magma G] (h : Equation36786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X4 ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X1) = X2 := superpose eq12 eq7
  have eq22 (X0 X2 X4 X5 : G) : ((X0 ◇ (X2 ◇ X4)) ◇ X5) = X2 := superpose eq7 eq9
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq22 eq16
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq43
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq106 eq44


@[equational_result]
theorem Equation36787_implies_Equation2 (G : Type*) [Magma G] (h : Equation36787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq10
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq109 eq30


@[equational_result]
theorem Equation36788_implies_Equation2 (G : Type*) [Magma G] (h : Equation36788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X6) = X4 := superpose eq7 eq7
  have eq34 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq10
  have eq46 (X0 X5 : G) : X0 = X5 := superpose eq7 eq34
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq106 eq46


@[equational_result]
theorem Equation36792_implies_Equation2 (G : Type*) [Magma G] (h : Equation36792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = (X0 ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq114 eq47


@[equational_result]
theorem Equation36794_implies_Equation2 (G : Type*) [Magma G] (h : Equation36794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ ((((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)))) ◇ ((X3 ◇ X0) ◇ ((((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)))))) ◇ ((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ ((((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)))) ◇ ((X3 ◇ X0) ◇ ((((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)))))))) ◇ ((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ ((((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)))) ◇ ((X3 ◇ X0) ◇ ((((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4))))))) = X2 := superpose eq9 eq9
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq9
  have eq32 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4))) ◇ ((X3 ◇ X0) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4))))) ◇ ((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4))) ◇ ((X3 ◇ X0) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4))))))) ◇ ((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4))) ◇ ((X3 ◇ X0) ◇ (((X4 ◇ X5) ◇ X3) ◇ (X4 ◇ X4)))))) = X2 := superpose eq26 eq21
  have eq47 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = X2 := superpose eq26 eq32
  have eq48 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) = X2 := superpose eq26 eq47
  have eq49 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq26 eq48
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq26 eq49
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq50 eq50
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq56 eq51


@[equational_result]
theorem Equation36795_implies_Equation2 (G : Type*) [Magma G] (h : Equation36795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X0))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = (X0 ◇ X2) := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))) ◇ (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))))) ◇ (X2 ◇ X2)) = X3 := superpose eq10 eq7
  have eq48 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := superpose eq15 eq10
  have eq55 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) = X3 := superpose eq15 eq7
  have eq89 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq48
  have eq96 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X1)) = (((X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq15 eq48
  have eq104 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq13 eq48
  have eq107 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq48 eq13
  have eq122 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X1) ◇ ((((X2 ◇ X0) ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X0) ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))))) ◇ (X2 ◇ X2)) = X3 := superpose eq104 eq17
  have eq128 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) = X3 := superpose eq15 eq122
  have eq132 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X2 := superpose eq128 eq107
  have eq134 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (X1 ◇ X1)) ◇ X2) = X3 := superpose eq132 eq9
  have eq143 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ (X1 ◇ X1)) = X3 := superpose eq132 eq89
  have eq207 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X1)) = X0 := superpose eq143 eq96
  have eq210 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = X3 := superpose eq207 eq55
  have eq225 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq134 eq134
  have eq232 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq225 eq210
  have eq234 (X0 X3 : G) : X0 = X3 := superpose eq48 eq232
  have eq287 (X0 : G) : sK0 ≠ X0 := superpose eq234 eq8
  subsumption eq287 eq234


@[equational_result]
theorem Equation36796_implies_Equation2 (G : Type*) [Magma G] (h : Equation36796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq128 eq45


@[equational_result]
theorem Equation36798_implies_Equation2 (G : Type*) [Magma G] (h : Equation36798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3))) = X4 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq9
  have eq63 (X0 X1 X2 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X2) = X2 := superpose eq20 eq7
  have eq66 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) ◇ X2) = X1 := superpose eq20 eq7
  have eq105 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq66 eq63
  have eq109 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3))) = X4 := superpose eq105 eq14
  have eq139 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X0) ◇ X3)) = X4 := superpose eq105 eq109
  have eq140 (X1 X2 X3 X4 : G) : ((X4 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) ◇ X3) = X4 := superpose eq105 eq139
  have eq141 (X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X3) = X4 := superpose eq105 eq140
  have eq142 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = X4 := superpose eq105 eq141
  have eq143 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq105 eq142
  have eq144 (X0 X3 : G) : X0 = X3 := superpose eq143 eq143
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq146 eq144


@[equational_result]
theorem Equation36799_implies_Equation2 (G : Type*) [Magma G] (h : Equation36799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq10 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq107 eq31


@[equational_result]
theorem Equation36800_implies_Equation2 (G : Type*) [Magma G] (h : Equation36800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ X3) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq121 eq41


@[equational_result]
theorem Equation36802_implies_Equation2 (G : Type*) [Magma G] (h : Equation36802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) ◇ X5)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq38
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq133 eq47


@[equational_result]
theorem Equation36803_implies_Equation2 (G : Type*) [Magma G] (h : Equation36803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq38 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X1 := superpose eq7 eq9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq38 eq38
  have eq114 (X0 X4 : G) : X0 = X4 := superpose eq7 eq56
  have eq241 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq241 eq114


@[equational_result]
theorem Equation36804_implies_Equation2 (G : Type*) [Magma G] (h : Equation36804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) ◇ X4) = X3 := superpose eq7 eq7
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq69 eq50


@[equational_result]
theorem Equation36805_implies_Equation2 (G : Type*) [Magma G] (h : Equation36805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X5 : G) : (X1 ◇ X3) = (X0 ◇ X5) := superpose eq7 eq7
  have eq15 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq47 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq131 eq47


@[equational_result]
theorem Equation36808_implies_Equation2 (G : Type*) [Magma G] (h : Equation36808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq9
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq12
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq157 eq74


@[equational_result]
theorem Equation36809_implies_Equation2 (G : Type*) [Magma G] (h : Equation36809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation36811_implies_Equation2 (G : Type*) [Magma G] (h : Equation36811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X0)) ◇ X0) = X2 := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq7 eq11
  have eq38 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq30
  have eq39 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq38 eq17
  have eq59 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq38 eq39
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq38 eq59
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq67 eq62


@[equational_result]
theorem Equation36813_implies_Equation2 (G : Type*) [Magma G] (h : Equation36813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4) = X3 := superpose eq7 eq7
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq71 eq54


@[equational_result]
theorem Equation36816_implies_Equation2 (G : Type*) [Magma G] (h : Equation36816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X2 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq9
  have eq15 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = (X0 ◇ X2) := superpose eq7 eq9
  have eq21 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq9
  have eq29 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq21 eq7
  have eq33 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq21 eq29
  have eq38 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq33 eq13
  have eq39 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X2) := superpose eq33 eq15
  have eq43 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq33 eq39
  have eq44 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq43 eq38
  have eq56 (X0 X1 : G) : X0 = X1 := superpose eq43 eq44
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq61 eq56


@[equational_result]
theorem Equation36817_implies_Equation2 (G : Type*) [Magma G] (h : Equation36817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq131 eq48


@[equational_result]
theorem Equation36819_implies_Equation2 (G : Type*) [Magma G] (h : Equation36819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X4))) ◇ X5) ◇ X0) ◇ X1) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X2) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) = X4 := superpose eq12 eq7
  have eq48 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X0) := superpose eq7 eq10
  have eq63 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X5) ◇ X0) ◇ X1) = X5 := superpose eq48 eq11
  have eq107 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X5) ◇ X6) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = X5 := superpose eq10 eq63
  have eq144 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq107 eq24
  have eq145 (X0 X4 : G) : X0 = X4 := superpose eq7 eq144
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq292 eq145


@[equational_result]
theorem Equation36820_implies_Equation2 (G : Type*) [Magma G] (h : Equation36820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3))) := superpose eq7 eq12
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq7 eq12
  have eq29 (X0 X1 X2 X4 : G) : (X0 ◇ X4) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq15 eq13
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq15 eq7
  have eq33 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq16 eq29
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq33 eq31
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq33 eq35
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation36821_implies_Equation2 (G : Type*) [Magma G] (h : Equation36821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X0 := superpose eq12 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation36822_implies_Equation2 (G : Type*) [Magma G] (h : Equation36822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 X5 : G) : (X2 ◇ X3) = (X0 ◇ X5) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation36824_implies_Equation2 (G : Type*) [Magma G] (h : Equation36824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq11 eq11
  have eq47 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq115 eq47


@[equational_result]
theorem Equation36825_implies_Equation2 (G : Type*) [Magma G] (h : Equation36825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : (X3 ◇ X0) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq7 eq12
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq89 eq46


@[equational_result]
theorem Equation36826_implies_Equation2 (G : Type*) [Magma G] (h : Equation36826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq10
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq107 eq30


@[equational_result]
theorem Equation36827_implies_Equation2 (G : Type*) [Magma G] (h : Equation36827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X3 ◇ X0) = (X0 ◇ X5) := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq12
  have eq45 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq105 eq45


@[equational_result]
theorem Equation36829_implies_Equation2 (G : Type*) [Magma G] (h : Equation36829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq11 eq11
  have eq41 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq126 eq41


@[equational_result]
theorem Equation36830_implies_Equation2 (G : Type*) [Magma G] (h : Equation36830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X4 := superpose eq7 eq11
  have eq22 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq12 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation36831_implies_Equation2 (G : Type*) [Magma G] (h : Equation36831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ X3) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq7 eq12
  have eq38 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = X3 := superpose eq19 eq10
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq7 eq38
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq68 eq45


@[equational_result]
theorem Equation36832_implies_Equation2 (G : Type*) [Magma G] (h : Equation36832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X5 : G) : (X3 ◇ X1) = (X0 ◇ X5) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq139 eq49


@[equational_result]
theorem Equation36834_implies_Equation2 (G : Type*) [Magma G] (h : Equation36834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) ◇ X5) ◇ X3) = X4 := superpose eq12 eq11
  have eq42 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X5) ◇ X3) = X2 := superpose eq12 eq11
  have eq53 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq42 eq37
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq134 eq54


@[equational_result]
theorem Equation36835_implies_Equation2 (G : Type*) [Magma G] (h : Equation36835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = X0 := superpose eq12 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36836_implies_Equation2 (G : Type*) [Magma G] (h : Equation36836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X4 ◇ (X3 ◇ X2))) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X0 ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ X5) = X4 := superpose eq12 eq9
  have eq17 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq15 eq12
  have eq18 (X0 X2 X3 X4 : G) : ((X0 ◇ (X4 ◇ X2)) ◇ X4) = X3 := superpose eq17 eq10
  have eq22 (X2 X3 X4 : G) : ((X4 ◇ X2) ◇ X4) = X3 := superpose eq17 eq18
  have eq23 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq17 eq22
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation36837_implies_Equation2 (G : Type*) [Magma G] (h : Equation36837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 X5 : G) : (X3 ◇ X2) = (X0 ◇ X5) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation36839_implies_Equation2 (G : Type*) [Magma G] (h : Equation36839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq154 eq56


@[equational_result]
theorem Equation36840_implies_Equation2 (G : Type*) [Magma G] (h : Equation36840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq9 eq9
  have eq43 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq28 eq7
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq9 eq43
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq103 eq44


@[equational_result]
theorem Equation36841_implies_Equation2 (G : Type*) [Magma G] (h : Equation36841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ X4) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation36842_implies_Equation2 (G : Type*) [Magma G] (h : Equation36842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ (X5 ◇ X5)) ◇ X6) = X4 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation36844_implies_Equation2 (G : Type*) [Magma G] (h : Equation36844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation36845_implies_Equation2 (G : Type*) [Magma G] (h : Equation36845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 : G) : (X5 ◇ X5) = X0 := superpose eq7 eq12
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq129 eq48


@[equational_result]
theorem Equation36846_implies_Equation2 (G : Type*) [Magma G] (h : Equation36846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation36847_implies_Equation2 (G : Type*) [Magma G] (h : Equation36847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X6) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation36848_implies_Equation2 (G : Type*) [Magma G] (h : Equation36848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 X8 : G) : ((X0 ◇ (X6 ◇ X7)) ◇ X8) = X5 := superpose eq7 eq7
  have eq39 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation36850_implies_Equation2 (G : Type*) [Magma G] (h : Equation36850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq7
  have eq21 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq7
  have eq26 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq21 eq11
  have eq29 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq26 eq26
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq21
  have eq45 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq29
  have eq49 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq45 eq7
  have eq55 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq45 eq26
  have eq69 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq45 eq55
  have eq73 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq69 eq49
  have eq86 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq73 eq73
  have eq87 (X0 X3 : G) : X0 = X3 := superpose eq73 eq86
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq94 eq87


@[equational_result]
theorem Equation36852_implies_Equation2 (G : Type*) [Magma G] (h : Equation36852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36854_implies_Equation2 (G : Type*) [Magma G] (h : Equation36854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)))) = (((((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ X3) ◇ X0) ◇ X5) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X4) ◇ ((X0 ◇ X3) ◇ X0)) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) ◇ (X4 ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = ((((X0 ◇ X4) ◇ X0) ◇ X2) ◇ X0) := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X4 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ X4) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq26 eq25
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X5) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X4) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq10 eq9
  have eq55 (X0 X1 X2 X4 X5 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X5) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X4) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq19 eq37
  have eq56 (X0 X1 X2 X4 X5 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X4) = ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X5) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X4) := superpose eq9 eq55
  have eq57 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq56 eq11
  have eq82 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X4 := superpose eq26 eq9
  have eq83 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X1))) = (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq26 eq10
  have eq84 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X3) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq26 eq10
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) = ((((((X1 ◇ X2) ◇ X1) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq26 eq10
  have eq94 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq35
  have eq112 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq94 eq26
  have eq169 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)) := superpose eq18 eq26
  have eq227 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq26 eq112
  have eq252 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)))) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq112 eq9
  have eq256 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq26 eq227
  have eq258 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)))) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq57 eq252
  have eq373 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq26 eq256
  have eq406 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq256 eq373
  have eq407 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq406 eq258
  have eq412 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq406 eq23
  have eq442 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq406 eq412
  have eq443 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq442 eq169
  have eq446 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq406 eq443
  have eq447 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X0 := superpose eq442 eq446
  have eq448 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) ◇ (X4 ◇ ((X0 ◇ X3) ◇ X0))) = ((((X0 ◇ X3) ◇ X0) ◇ X4) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq447 eq13
  have eq450 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq447 eq83
  have eq451 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) = ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq447 eq85
  have eq460 (X0 X1 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X3) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq447 eq84
  have eq461 (X0 X1 X2 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X4 := superpose eq447 eq82
  have eq472 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq447 eq407
  have eq540 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X0) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) ◇ (X4 ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq447 eq448
  have eq541 (X0 X1 X2 X4 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ X0)) = X0 := superpose eq447 eq540
  have eq542 (X0 X2 X4 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ X0)) = X0 := superpose eq447 eq541
  have eq543 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X0)) = X0 := superpose eq447 eq542
  have eq544 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X0 := superpose eq406 eq543
  have eq550 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X1) = (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq544 eq450
  have eq551 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X4) ◇ X1) = X1 := superpose eq447 eq550
  have eq552 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq447 eq451
  have eq553 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X1)) = X1 := superpose eq447 eq552
  have eq562 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq551 eq460
  have eq563 (X0 X1 X2 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) = X4 := superpose eq562 eq461
  have eq564 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X4 := superpose eq553 eq563
  have eq575 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq553 eq472
  have eq577 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq575 eq564
  have eq586 (X0 X2 : G) : X0 = X2 := superpose eq577 eq577
  have eq588 (X0 : G) : sK0 ≠ X0 := superpose eq586 eq8
  subsumption eq588 eq586


@[equational_result]
theorem Equation36855_implies_Equation2 (G : Type*) [Magma G] (h : Equation36855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ X3) ◇ (X0 ◇ X3)) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ ((X2 ◇ X4) ◇ X3)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) ◇ X0) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := superpose eq7 eq10
  have eq36 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq26 eq25
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq36
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq26 eq91
  have eq116 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1) = X2 := superpose eq91 eq9
  have eq136 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq109 eq7
  have eq295 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X2 := superpose eq136 eq116
  have eq296 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X2 := superpose eq109 eq295
  have eq297 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq91 eq296
  have eq307 (X0 X1 : G) : X0 = X1 := superpose eq91 eq297
  have eq373 (X0 : G) : sK0 ≠ X0 := superpose eq307 eq8
  subsumption eq373 eq307


@[equational_result]
theorem Equation36856_implies_Equation2 (G : Type*) [Magma G] (h : Equation36856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation36858_implies_Equation2 (G : Type*) [Magma G] (h : Equation36858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X3)) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((((X5 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X5) ◇ X4) ◇ X5) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ ((X2 ◇ X3) ◇ X4)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq26 eq25
  have eq97 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq7 eq35
  have eq124 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq97 eq35
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) := superpose eq97 eq9
  have eq146 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq26 eq131
  have eq147 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq124 eq146
  have eq148 (X0 X1 X2 X3 X4 X5 : G) : ((((X5 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X5) ◇ X4) ◇ X5) = ((X0 ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X4 ◇ (X2 ◇ X3))) := superpose eq147 eq13
  have eq236 (X0 X1 X2 X3 X4 X5 : G) : ((((X5 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X5) ◇ X4) ◇ X5) = ((X0 ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X2 ◇ X3)) := superpose eq147 eq148
  have eq237 (X0 X1 X3 X4 X5 : G) : ((((X5 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X5) ◇ X4) ◇ X5) = ((X0 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X3) := superpose eq147 eq236
  have eq238 (X1 X3 X4 X5 : G) : ((((X5 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X5) ◇ X4) ◇ X5) = X3 := superpose eq147 eq237
  have eq239 (X3 X4 X5 : G) : (X4 ◇ X5) = X3 := superpose eq147 eq238
  have eq240 (X0 X3 : G) : X0 = X3 := superpose eq239 eq239
  have eq242 (X0 : G) : sK0 ≠ X0 := superpose eq240 eq8
  subsumption eq242 eq240


@[equational_result]
theorem Equation36859_implies_Equation2 (G : Type*) [Magma G] (h : Equation36859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation36860_implies_Equation2 (G : Type*) [Magma G] (h : Equation36860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation36862_implies_Equation2 (G : Type*) [Magma G] (h : Equation36862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq11 eq11
  have eq22 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X0 := superpose eq15 eq7
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq22 eq15
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq75 eq34


@[equational_result]
theorem Equation36863_implies_Equation2 (G : Type*) [Magma G] (h : Equation36863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation36864_implies_Equation2 (G : Type*) [Magma G] (h : Equation36864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36865_implies_Equation2 (G : Type*) [Magma G] (h : Equation36865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation36869_implies_Equation2 (G : Type*) [Magma G] (h : Equation36869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation36871_implies_Equation2 (G : Type*) [Magma G] (h : Equation36871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36872_implies_Equation2 (G : Type*) [Magma G] (h : Equation36872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36873_implies_Equation2 (G : Type*) [Magma G] (h : Equation36873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36875_implies_Equation2 (G : Type*) [Magma G] (h : Equation36875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36876_implies_Equation2 (G : Type*) [Magma G] (h : Equation36876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36877_implies_Equation2 (G : Type*) [Magma G] (h : Equation36877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36879_implies_Equation2 (G : Type*) [Magma G] (h : Equation36879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36880_implies_Equation2 (G : Type*) [Magma G] (h : Equation36880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36881_implies_Equation2 (G : Type*) [Magma G] (h : Equation36881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36882_implies_Equation2 (G : Type*) [Magma G] (h : Equation36882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36886_implies_Equation2 (G : Type*) [Magma G] (h : Equation36886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation36888_implies_Equation2 (G : Type*) [Magma G] (h : Equation36888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36889_implies_Equation2 (G : Type*) [Magma G] (h : Equation36889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36890_implies_Equation2 (G : Type*) [Magma G] (h : Equation36890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36892_implies_Equation2 (G : Type*) [Magma G] (h : Equation36892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36893_implies_Equation2 (G : Type*) [Magma G] (h : Equation36893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36894_implies_Equation2 (G : Type*) [Magma G] (h : Equation36894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36896_implies_Equation2 (G : Type*) [Magma G] (h : Equation36896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36897_implies_Equation2 (G : Type*) [Magma G] (h : Equation36897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36898_implies_Equation2 (G : Type*) [Magma G] (h : Equation36898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36899_implies_Equation2 (G : Type*) [Magma G] (h : Equation36899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36901_implies_Equation2 (G : Type*) [Magma G] (h : Equation36901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq45 eq28


@[equational_result]
theorem Equation36902_implies_Equation2 (G : Type*) [Magma G] (h : Equation36902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X0))) ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq11 eq9
  have eq15 (X1 X2 X5 : G) : (X1 ◇ X2) = X5 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation36903_implies_Equation2 (G : Type*) [Magma G] (h : Equation36903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36904_implies_Equation2 (G : Type*) [Magma G] (h : Equation36904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation36906_implies_Equation2 (G : Type*) [Magma G] (h : Equation36906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36907_implies_Equation2 (G : Type*) [Magma G] (h : Equation36907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36908_implies_Equation2 (G : Type*) [Magma G] (h : Equation36908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36909_implies_Equation2 (G : Type*) [Magma G] (h : Equation36909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36911_implies_Equation2 (G : Type*) [Magma G] (h : Equation36911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36912_implies_Equation2 (G : Type*) [Magma G] (h : Equation36912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36913_implies_Equation2 (G : Type*) [Magma G] (h : Equation36913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36914_implies_Equation2 (G : Type*) [Magma G] (h : Equation36914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36916_implies_Equation2 (G : Type*) [Magma G] (h : Equation36916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36917_implies_Equation2 (G : Type*) [Magma G] (h : Equation36917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36918_implies_Equation2 (G : Type*) [Magma G] (h : Equation36918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36919_implies_Equation2 (G : Type*) [Magma G] (h : Equation36919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36921_implies_Equation2 (G : Type*) [Magma G] (h : Equation36921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36922_implies_Equation2 (G : Type*) [Magma G] (h : Equation36922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36923_implies_Equation2 (G : Type*) [Magma G] (h : Equation36923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36924_implies_Equation2 (G : Type*) [Magma G] (h : Equation36924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36925_implies_Equation2 (G : Type*) [Magma G] (h : Equation36925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36928_implies_Equation2 (G : Type*) [Magma G] (h : Equation36928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq54 eq26


@[equational_result]
theorem Equation36929_implies_Equation2 (G : Type*) [Magma G] (h : Equation36929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36931_implies_Equation2 (G : Type*) [Magma G] (h : Equation36931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X3) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = ((((X0 ◇ X4) ◇ X4) ◇ X2) ◇ X0) := superpose eq10 eq10
  have eq27 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ ((X2 ◇ X0) ◇ X0)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq28 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X4) = (((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq10 eq7
  have eq40 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq28 eq27
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) := superpose eq10 eq28
  have eq84 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq28 eq28
  have eq89 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2)))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) = X3 := superpose eq28 eq9
  have eq103 (X0 X2 X4 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = ((X0 ◇ X4) ◇ X4) := superpose eq83 eq32
  have eq141 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq103
  have eq259 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq19 eq28
  have eq368 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) = X0 := superpose eq28 eq141
  have eq398 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq141 eq40
  have eq483 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq398 eq84
  have eq485 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq483 eq89
  have eq488 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq483 eq368
  have eq493 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq488 eq259
  have eq616 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X3) = X3 := superpose eq488 eq493
  have eq617 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq488 eq616
  have eq619 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq617 eq485
  have eq624 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X3 := superpose eq617 eq619
  have eq625 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X3 := superpose eq617 eq624
  have eq626 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq617 eq625
  have eq765 (X0 X1 : G) : X0 = X1 := superpose eq617 eq626
  have eq775 (X0 : G) : sK0 ≠ X0 := superpose eq765 eq8
  subsumption eq775 eq765


@[equational_result]
theorem Equation36933_implies_Equation2 (G : Type*) [Magma G] (h : Equation36933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation36936_implies_Equation2 (G : Type*) [Magma G] (h : Equation36936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((X3 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = ((((X4 ◇ X2) ◇ X2) ◇ (((X3 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X2) := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3) ◇ X1) := superpose eq10 eq10
  have eq33 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq10
  have eq34 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq7 eq10
  have eq40 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X1) = ((((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq10 eq7
  have eq51 (X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq33
  have eq52 (X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) = ((X1 ◇ X3) ◇ X1) := superpose eq51 eq31
  have eq55 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = ((((X4 ◇ X2) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) := superpose eq52 eq22
  have eq56 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq52 eq13
  have eq61 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (X2 ◇ X0) := superpose eq9 eq55
  have eq62 (X1 X3 : G) : ((X1 ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ X1)) := superpose eq61 eq52
  have eq73 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X2)) := superpose eq62 eq56
  have eq74 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ X2)) := superpose eq73 eq14
  have eq85 (X0 X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X1) = (((X2 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq61 eq40
  have eq86 (X0 X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X1) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq74 eq85
  have eq87 (X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) := superpose eq73 eq86
  have eq88 (X1 X4 : G) : ((X4 ◇ X1) ◇ X1) = X1 := superpose eq11 eq87
  have eq89 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq88 eq34
  have eq92 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq88 eq89
  have eq107 (X0 X2 : G) : X0 = X2 := superpose eq92 eq92
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq113 eq107


@[equational_result]
theorem Equation36937_implies_Equation2 (G : Type*) [Magma G] (h : Equation36937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq9
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq138 eq36


@[equational_result]
theorem Equation36939_implies_Equation2 (G : Type*) [Magma G] (h : Equation36939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq12 eq10
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq37
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq139 eq48


@[equational_result]
theorem Equation36940_implies_Equation2 (G : Type*) [Magma G] (h : Equation36940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X4) ◇ (X0 ◇ X5)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq12 eq7
  have eq18 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X4) ◇ (X0 ◇ X5)) = X0 := superpose eq16 eq11
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq18 eq7
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq20 eq16
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq20 eq21
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq20 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq37 eq29


@[equational_result]
theorem Equation36941_implies_Equation2 (G : Type*) [Magma G] (h : Equation36941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation36942_implies_Equation2 (G : Type*) [Magma G] (h : Equation36942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36946_implies_Equation2 (G : Type*) [Magma G] (h : Equation36946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation36948_implies_Equation2 (G : Type*) [Magma G] (h : Equation36948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36949_implies_Equation2 (G : Type*) [Magma G] (h : Equation36949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36950_implies_Equation2 (G : Type*) [Magma G] (h : Equation36950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36952_implies_Equation2 (G : Type*) [Magma G] (h : Equation36952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36953_implies_Equation2 (G : Type*) [Magma G] (h : Equation36953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation36954_implies_Equation2 (G : Type*) [Magma G] (h : Equation36954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36956_implies_Equation2 (G : Type*) [Magma G] (h : Equation36956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36957_implies_Equation2 (G : Type*) [Magma G] (h : Equation36957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36958_implies_Equation2 (G : Type*) [Magma G] (h : Equation36958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36959_implies_Equation2 (G : Type*) [Magma G] (h : Equation36959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36962_implies_Equation2 (G : Type*) [Magma G] (h : Equation36962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq9
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq11
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq183 eq75


@[equational_result]
theorem Equation36963_implies_Equation2 (G : Type*) [Magma G] (h : Equation36963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ X0))) ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ X0))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq9
  have eq21 (X0 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ X5) = X4 := superpose eq12 eq11
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation36965_implies_Equation2 (G : Type*) [Magma G] (h : Equation36965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36966_implies_Equation2 (G : Type*) [Magma G] (h : Equation36966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36967_implies_Equation2 (G : Type*) [Magma G] (h : Equation36967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36969_implies_Equation2 (G : Type*) [Magma G] (h : Equation36969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36970_implies_Equation2 (G : Type*) [Magma G] (h : Equation36970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation36971_implies_Equation2 (G : Type*) [Magma G] (h : Equation36971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36973_implies_Equation2 (G : Type*) [Magma G] (h : Equation36973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36974_implies_Equation2 (G : Type*) [Magma G] (h : Equation36974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36975_implies_Equation2 (G : Type*) [Magma G] (h : Equation36975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36976_implies_Equation2 (G : Type*) [Magma G] (h : Equation36976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36978_implies_Equation2 (G : Type*) [Magma G] (h : Equation36978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation36979_implies_Equation2 (G : Type*) [Magma G] (h : Equation36979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq12
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq13 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq13 eq18
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation36980_implies_Equation2 (G : Type*) [Magma G] (h : Equation36980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation36981_implies_Equation2 (G : Type*) [Magma G] (h : Equation36981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation36983_implies_Equation2 (G : Type*) [Magma G] (h : Equation36983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36984_implies_Equation2 (G : Type*) [Magma G] (h : Equation36984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36985_implies_Equation2 (G : Type*) [Magma G] (h : Equation36985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36986_implies_Equation2 (G : Type*) [Magma G] (h : Equation36986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36988_implies_Equation2 (G : Type*) [Magma G] (h : Equation36988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36989_implies_Equation2 (G : Type*) [Magma G] (h : Equation36989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36990_implies_Equation2 (G : Type*) [Magma G] (h : Equation36990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36991_implies_Equation2 (G : Type*) [Magma G] (h : Equation36991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36993_implies_Equation2 (G : Type*) [Magma G] (h : Equation36993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36994_implies_Equation2 (G : Type*) [Magma G] (h : Equation36994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation36995_implies_Equation2 (G : Type*) [Magma G] (h : Equation36995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation36996_implies_Equation2 (G : Type*) [Magma G] (h : Equation36996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36998_implies_Equation2 (G : Type*) [Magma G] (h : Equation36998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation36999_implies_Equation2 (G : Type*) [Magma G] (h : Equation36999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37000_implies_Equation2 (G : Type*) [Magma G] (h : Equation37000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37001_implies_Equation2 (G : Type*) [Magma G] (h : Equation37001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37002_implies_Equation2 (G : Type*) [Magma G] (h : Equation37002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37004_implies_Equation2 (G : Type*) [Magma G] (h : Equation37004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq40 eq15


@[equational_result]
theorem Equation37005_implies_Equation2 (G : Type*) [Magma G] (h : Equation37005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation37006_implies_Equation2 (G : Type*) [Magma G] (h : Equation37006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq37 eq13


@[equational_result]
theorem Equation37007_implies_Equation2 (G : Type*) [Magma G] (h : Equation37007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation37009_implies_Equation2 (G : Type*) [Magma G] (h : Equation37009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))) ◇ ((X1 ◇ X2) ◇ X3)) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (X3 ◇ X4) := superpose eq10 eq7
  have eq71 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq20
  have eq179 (X0 X4 : G) : X0 = X4 := superpose eq7 eq71
  have eq335 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq335 eq179


@[equational_result]
theorem Equation37010_implies_Equation2 (G : Type*) [Magma G] (h : Equation37010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)))) ◇ X2) = X5 := superpose eq7 eq7
  have eq43 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq9 eq9
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq43
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq189 eq60


@[equational_result]
theorem Equation37011_implies_Equation2 (G : Type*) [Magma G] (h : Equation37011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation37012_implies_Equation2 (G : Type*) [Magma G] (h : Equation37012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation37014_implies_Equation2 (G : Type*) [Magma G] (h : Equation37014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq45 eq17


@[equational_result]
theorem Equation37015_implies_Equation2 (G : Type*) [Magma G] (h : Equation37015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37016_implies_Equation2 (G : Type*) [Magma G] (h : Equation37016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X5 ◇ X3)) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X4 ◇ (X0 ◇ X2))) ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X3) = X4 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X5) := superpose eq7 eq10
  have eq35 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X5) = X1 := superpose eq12 eq24
  have eq40 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq35 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq10 eq40
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq72 eq41


@[equational_result]
theorem Equation37017_implies_Equation2 (G : Type*) [Magma G] (h : Equation37017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37019_implies_Equation2 (G : Type*) [Magma G] (h : Equation37019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X4 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq12 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq44 eq35


@[equational_result]
theorem Equation37020_implies_Equation2 (G : Type*) [Magma G] (h : Equation37020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37021_implies_Equation2 (G : Type*) [Magma G] (h : Equation37021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ X3) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq10
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq135 eq30


@[equational_result]
theorem Equation37022_implies_Equation2 (G : Type*) [Magma G] (h : Equation37022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation37024_implies_Equation2 (G : Type*) [Magma G] (h : Equation37024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation37025_implies_Equation2 (G : Type*) [Magma G] (h : Equation37025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37026_implies_Equation2 (G : Type*) [Magma G] (h : Equation37026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation37027_implies_Equation2 (G : Type*) [Magma G] (h : Equation37027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation37028_implies_Equation2 (G : Type*) [Magma G] (h : Equation37028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation37030_implies_Equation2 (G : Type*) [Magma G] (h : Equation37030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ ((X1 ◇ X2) ◇ X3)) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = X4 := superpose eq10 eq7
  have eq55 (X0 X5 : G) : X0 = X5 := superpose eq7 eq20
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq148 eq55


@[equational_result]
theorem Equation37031_implies_Equation2 (G : Type*) [Magma G] (h : Equation37031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) ◇ X5)) ◇ X2) = X5 := superpose eq7 eq7
  have eq42 (X0 X5 X7 : G) : (X0 ◇ X5) = X7 := superpose eq9 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq42
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq133 eq67


@[equational_result]
theorem Equation37032_implies_Equation2 (G : Type*) [Magma G] (h : Equation37032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation37033_implies_Equation2 (G : Type*) [Magma G] (h : Equation37033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation37035_implies_Equation2 (G : Type*) [Magma G] (h : Equation37035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37036_implies_Equation2 (G : Type*) [Magma G] (h : Equation37036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37037_implies_Equation2 (G : Type*) [Magma G] (h : Equation37037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37038_implies_Equation2 (G : Type*) [Magma G] (h : Equation37038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37040_implies_Equation2 (G : Type*) [Magma G] (h : Equation37040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37041_implies_Equation2 (G : Type*) [Magma G] (h : Equation37041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37042_implies_Equation2 (G : Type*) [Magma G] (h : Equation37042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


