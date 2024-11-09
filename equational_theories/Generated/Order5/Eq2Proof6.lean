import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation14214_implies_Equation2 (G : Type*) [Magma G] (h : Equation14214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14215_implies_Equation2 (G : Type*) [Magma G] (h : Equation14215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14217_implies_Equation2 (G : Type*) [Magma G] (h : Equation14217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X4))) ◇ X0) = X5 := superpose eq7 eq7
  have eq187 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq11 eq11
  have eq208 (X0 X4 : G) : X0 = X4 := superpose eq7 eq187
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq208 eq8
  subsumption eq360 eq208


@[equational_result]
theorem Equation14218_implies_Equation2 (G : Type*) [Magma G] (h : Equation14218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14219_implies_Equation2 (G : Type*) [Magma G] (h : Equation14219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation14220_implies_Equation2 (G : Type*) [Magma G] (h : Equation14220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14222_implies_Equation2 (G : Type*) [Magma G] (h : Equation14222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation14223_implies_Equation2 (G : Type*) [Magma G] (h : Equation14223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14224_implies_Equation2 (G : Type*) [Magma G] (h : Equation14224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14225_implies_Equation2 (G : Type*) [Magma G] (h : Equation14225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X5 ◇ ((X6 ◇ X0) ◇ X7)) ◇ X7))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation14226_implies_Equation2 (G : Type*) [Magma G] (h : Equation14226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14228_implies_Equation2 (G : Type*) [Magma G] (h : Equation14228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X3 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X0) := superpose eq7 eq11
  have eq21 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq16 eq15
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq11 eq21
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq157 eq65


@[equational_result]
theorem Equation14229_implies_Equation2 (G : Type*) [Magma G] (h : Equation14229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq67 eq21


@[equational_result]
theorem Equation14230_implies_Equation2 (G : Type*) [Magma G] (h : Equation14230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) ◇ ((X4 ◇ (X0 ◇ X5)) ◇ X3)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X1 := superpose eq7 eq7
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq11 eq9
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq50 eq41


@[equational_result]
theorem Equation14231_implies_Equation2 (G : Type*) [Magma G] (h : Equation14231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq56 eq13


@[equational_result]
theorem Equation14233_implies_Equation2 (G : Type*) [Magma G] (h : Equation14233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14234_implies_Equation2 (G : Type*) [Magma G] (h : Equation14234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14235_implies_Equation2 (G : Type*) [Magma G] (h : Equation14235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14236_implies_Equation2 (G : Type*) [Magma G] (h : Equation14236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14238_implies_Equation2 (G : Type*) [Magma G] (h : Equation14238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14239_implies_Equation2 (G : Type*) [Magma G] (h : Equation14239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14240_implies_Equation2 (G : Type*) [Magma G] (h : Equation14240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14241_implies_Equation2 (G : Type*) [Magma G] (h : Equation14241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14243_implies_Equation2 (G : Type*) [Magma G] (h : Equation14243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14244_implies_Equation2 (G : Type*) [Magma G] (h : Equation14244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14245_implies_Equation2 (G : Type*) [Magma G] (h : Equation14245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14246_implies_Equation2 (G : Type*) [Magma G] (h : Equation14246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14248_implies_Equation2 (G : Type*) [Magma G] (h : Equation14248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14249_implies_Equation2 (G : Type*) [Magma G] (h : Equation14249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14250_implies_Equation2 (G : Type*) [Magma G] (h : Equation14250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14251_implies_Equation2 (G : Type*) [Magma G] (h : Equation14251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14252_implies_Equation2 (G : Type*) [Magma G] (h : Equation14252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14254_implies_Equation2 (G : Type*) [Magma G] (h : Equation14254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X5))) ◇ X0) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X0))) = X0 := superpose eq7 eq11
  have eq35 (X0 X5 : G) : (X5 ◇ X0) = X5 := superpose eq22 eq12
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq35 eq7
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq35 eq36
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq51 eq49


@[equational_result]
theorem Equation14255_implies_Equation2 (G : Type*) [Magma G] (h : Equation14255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ X5)) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14256_implies_Equation2 (G : Type*) [Magma G] (h : Equation14256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14257_implies_Equation2 (G : Type*) [Magma G] (h : Equation14257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14259_implies_Equation2 (G : Type*) [Magma G] (h : Equation14259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14260_implies_Equation2 (G : Type*) [Magma G] (h : Equation14260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14261_implies_Equation2 (G : Type*) [Magma G] (h : Equation14261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14262_implies_Equation2 (G : Type*) [Magma G] (h : Equation14262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14264_implies_Equation2 (G : Type*) [Magma G] (h : Equation14264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14265_implies_Equation2 (G : Type*) [Magma G] (h : Equation14265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14266_implies_Equation2 (G : Type*) [Magma G] (h : Equation14266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14267_implies_Equation2 (G : Type*) [Magma G] (h : Equation14267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14269_implies_Equation2 (G : Type*) [Magma G] (h : Equation14269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14270_implies_Equation2 (G : Type*) [Magma G] (h : Equation14270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14271_implies_Equation2 (G : Type*) [Magma G] (h : Equation14271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14272_implies_Equation2 (G : Type*) [Magma G] (h : Equation14272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14274_implies_Equation2 (G : Type*) [Magma G] (h : Equation14274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14275_implies_Equation2 (G : Type*) [Magma G] (h : Equation14275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14276_implies_Equation2 (G : Type*) [Magma G] (h : Equation14276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14277_implies_Equation2 (G : Type*) [Magma G] (h : Equation14277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14278_implies_Equation2 (G : Type*) [Magma G] (h : Equation14278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14280_implies_Equation2 (G : Type*) [Magma G] (h : Equation14280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation14281_implies_Equation2 (G : Type*) [Magma G] (h : Equation14281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14282_implies_Equation2 (G : Type*) [Magma G] (h : Equation14282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ ((X3 ◇ ((X4 ◇ X4) ◇ X0)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14283_implies_Equation2 (G : Type*) [Magma G] (h : Equation14283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14285_implies_Equation2 (G : Type*) [Magma G] (h : Equation14285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14286_implies_Equation2 (G : Type*) [Magma G] (h : Equation14286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14287_implies_Equation2 (G : Type*) [Magma G] (h : Equation14287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14288_implies_Equation2 (G : Type*) [Magma G] (h : Equation14288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14290_implies_Equation2 (G : Type*) [Magma G] (h : Equation14290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14291_implies_Equation2 (G : Type*) [Magma G] (h : Equation14291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14292_implies_Equation2 (G : Type*) [Magma G] (h : Equation14292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14293_implies_Equation2 (G : Type*) [Magma G] (h : Equation14293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14295_implies_Equation2 (G : Type*) [Magma G] (h : Equation14295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14296_implies_Equation2 (G : Type*) [Magma G] (h : Equation14296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14297_implies_Equation2 (G : Type*) [Magma G] (h : Equation14297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14298_implies_Equation2 (G : Type*) [Magma G] (h : Equation14298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14300_implies_Equation2 (G : Type*) [Magma G] (h : Equation14300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14301_implies_Equation2 (G : Type*) [Magma G] (h : Equation14301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14302_implies_Equation2 (G : Type*) [Magma G] (h : Equation14302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14303_implies_Equation2 (G : Type*) [Magma G] (h : Equation14303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14304_implies_Equation2 (G : Type*) [Magma G] (h : Equation14304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14306_implies_Equation2 (G : Type*) [Magma G] (h : Equation14306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation14307_implies_Equation2 (G : Type*) [Magma G] (h : Equation14307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14308_implies_Equation2 (G : Type*) [Magma G] (h : Equation14308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14309_implies_Equation2 (G : Type*) [Magma G] (h : Equation14309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X7)) ◇ ((X4 ◇ ((X5 ◇ X6) ◇ X0)) ◇ X6))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14310_implies_Equation2 (G : Type*) [Magma G] (h : Equation14310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14312_implies_Equation2 (G : Type*) [Magma G] (h : Equation14312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14313_implies_Equation2 (G : Type*) [Magma G] (h : Equation14313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14314_implies_Equation2 (G : Type*) [Magma G] (h : Equation14314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14315_implies_Equation2 (G : Type*) [Magma G] (h : Equation14315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14316_implies_Equation2 (G : Type*) [Magma G] (h : Equation14316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14318_implies_Equation2 (G : Type*) [Magma G] (h : Equation14318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14319_implies_Equation2 (G : Type*) [Magma G] (h : Equation14319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14320_implies_Equation2 (G : Type*) [Magma G] (h : Equation14320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14321_implies_Equation2 (G : Type*) [Magma G] (h : Equation14321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14322_implies_Equation2 (G : Type*) [Magma G] (h : Equation14322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X2)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14324_implies_Equation2 (G : Type*) [Magma G] (h : Equation14324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14325_implies_Equation2 (G : Type*) [Magma G] (h : Equation14325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14326_implies_Equation2 (G : Type*) [Magma G] (h : Equation14326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14327_implies_Equation2 (G : Type*) [Magma G] (h : Equation14327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14328_implies_Equation2 (G : Type*) [Magma G] (h : Equation14328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14330_implies_Equation2 (G : Type*) [Magma G] (h : Equation14330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14331_implies_Equation2 (G : Type*) [Magma G] (h : Equation14331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14332_implies_Equation2 (G : Type*) [Magma G] (h : Equation14332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14333_implies_Equation2 (G : Type*) [Magma G] (h : Equation14333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14334_implies_Equation2 (G : Type*) [Magma G] (h : Equation14334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14336_implies_Equation2 (G : Type*) [Magma G] (h : Equation14336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14337_implies_Equation2 (G : Type*) [Magma G] (h : Equation14337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14338_implies_Equation2 (G : Type*) [Magma G] (h : Equation14338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14339_implies_Equation2 (G : Type*) [Magma G] (h : Equation14339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14340_implies_Equation2 (G : Type*) [Magma G] (h : Equation14340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14341_implies_Equation2 (G : Type*) [Magma G] (h : Equation14341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14547_implies_Equation2 (G : Type*) [Magma G] (h : Equation14547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation14550_implies_Equation2 (G : Type*) [Magma G] (h : Equation14550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation14552_implies_Equation2 (G : Type*) [Magma G] (h : Equation14552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq130 eq58


@[equational_result]
theorem Equation14553_implies_Equation2 (G : Type*) [Magma G] (h : Equation14553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation14554_implies_Equation2 (G : Type*) [Magma G] (h : Equation14554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14557_implies_Equation2 (G : Type*) [Magma G] (h : Equation14557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation14560_implies_Equation2 (G : Type*) [Magma G] (h : Equation14560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq43 eq11


@[equational_result]
theorem Equation14562_implies_Equation2 (G : Type*) [Magma G] (h : Equation14562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)))) = X1 := superpose eq7 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq30 eq24


@[equational_result]
theorem Equation14563_implies_Equation2 (G : Type*) [Magma G] (h : Equation14563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq10 eq9
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq9
  have eq29 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq7 eq9
  have eq35 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq29 eq13
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq35 eq19
  have eq51 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose eq35 eq25
  have eq54 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq35 eq29
  have eq69 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq35 eq45
  have eq70 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := superpose eq35 eq69
  have eq84 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X1 := superpose eq35 eq51
  have eq85 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq35 eq84
  have eq90 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq54 eq85
  have eq91 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := superpose eq90 eq70
  have eq108 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq90 eq91
  have eq109 (X0 X1 : G) : X0 = X1 := superpose eq35 eq108
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq117 eq109


@[equational_result]
theorem Equation14564_implies_Equation2 (G : Type*) [Magma G] (h : Equation14564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14566_implies_Equation2 (G : Type*) [Magma G] (h : Equation14566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose eq10 eq7
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq16
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq169 eq75


@[equational_result]
theorem Equation14567_implies_Equation2 (G : Type*) [Magma G] (h : Equation14567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation14568_implies_Equation2 (G : Type*) [Magma G] (h : Equation14568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation14570_implies_Equation2 (G : Type*) [Magma G] (h : Equation14570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq27 eq12


@[equational_result]
theorem Equation14572_implies_Equation2 (G : Type*) [Magma G] (h : Equation14572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation14574_implies_Equation2 (G : Type*) [Magma G] (h : Equation14574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq35 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = X1 := superpose eq9 eq10
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) = X1 := superpose eq10 eq10
  have eq44 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq15 eq36
  have eq45 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) = X1 := superpose eq44 eq35
  have eq66 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq44 eq45
  have eq67 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq44 eq66
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq67 eq67
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq73 eq68


@[equational_result]
theorem Equation14575_implies_Equation2 (G : Type*) [Magma G] (h : Equation14575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation14576_implies_Equation2 (G : Type*) [Magma G] (h : Equation14576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14578_implies_Equation2 (G : Type*) [Magma G] (h : Equation14578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation14579_implies_Equation2 (G : Type*) [Magma G] (h : Equation14579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14580_implies_Equation2 (G : Type*) [Magma G] (h : Equation14580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X4 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation14581_implies_Equation2 (G : Type*) [Magma G] (h : Equation14581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14584_implies_Equation2 (G : Type*) [Magma G] (h : Equation14584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation14587_implies_Equation2 (G : Type*) [Magma G] (h : Equation14587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq43 eq11


@[equational_result]
theorem Equation14589_implies_Equation2 (G : Type*) [Magma G] (h : Equation14589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq108 eq38


@[equational_result]
theorem Equation14590_implies_Equation2 (G : Type*) [Magma G] (h : Equation14590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X0) := superpose eq9 eq7
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) = (X1 ◇ ((((X2 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq9 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X4)) ◇ X4))) := superpose eq10 eq9
  have eq43 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) ◇ X2) := superpose eq7 eq37
  have eq60 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ X3))) = X0 := superpose eq21 eq10
  have eq66 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X3)))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X3))) ◇ X4)) ◇ X4))) = X1 := superpose eq21 eq10
  have eq76 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X0) ◇ (X2 ◇ X4)) ◇ X4) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := superpose eq9 eq43
  have eq118 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) = X1 := superpose eq76 eq76
  have eq166 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq118 eq36
  have eq169 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ X3))) = X0 := superpose eq118 eq60
  have eq173 (X0 X1 X2 X4 : G) : (X2 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X4)) ◇ X4))) = X1 := superpose eq118 eq66
  have eq225 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq118 eq169
  have eq226 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq118 eq173
  have eq228 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq226 eq166
  have eq288 (X0 X1 : G) : X0 = X1 := superpose eq228 eq225
  have eq298 (X0 : G) : sK0 ≠ X0 := superpose eq288 eq8
  subsumption eq298 eq288


@[equational_result]
theorem Equation14591_implies_Equation2 (G : Type*) [Magma G] (h : Equation14591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14594_implies_Equation2 (G : Type*) [Magma G] (h : Equation14594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq53 eq12


@[equational_result]
theorem Equation14597_implies_Equation2 (G : Type*) [Magma G] (h : Equation14597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation14599_implies_Equation2 (G : Type*) [Magma G] (h : Equation14599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq107 eq36


@[equational_result]
theorem Equation14601_implies_Equation2 (G : Type*) [Magma G] (h : Equation14601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14603_implies_Equation2 (G : Type*) [Magma G] (h : Equation14603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X3 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) = X1 := superpose eq7 eq9
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq7 eq13
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq90 eq42


@[equational_result]
theorem Equation14605_implies_Equation2 (G : Type*) [Magma G] (h : Equation14605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14607_implies_Equation2 (G : Type*) [Magma G] (h : Equation14607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (((X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) = ((((X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0) ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ (X4 ◇ (((X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0) ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0) ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)))) := superpose eq7 eq9
  have eq37 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq37 eq7
  have eq79 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq65
  have eq110 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq79 eq79
  have eq114 (X0 X2 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = X2 := superpose eq79 eq10
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq79 eq9
  have eq116 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq79 eq7
  have eq119 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq79 eq7
  have eq189 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))))) := superpose eq79 eq14
  have eq230 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = (((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq11 eq114
  have eq236 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq116 eq114
  have eq253 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq236 eq79
  have eq254 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq236 eq110
  have eq257 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq236 eq119
  have eq265 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))))) := superpose eq236 eq189
  have eq274 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq253 eq257
  have eq275 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq116 eq274
  have eq296 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq275 eq265
  have eq297 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq254 eq296
  have eq298 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq275 eq297
  have eq299 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq115 eq298
  have eq300 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq236 eq299
  have eq343 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq300 eq230
  have eq453 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq300 eq7
  have eq480 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq453 eq343
  have eq484 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq480 eq7
  have eq656 (X0 X2 : G) : X0 = X2 := superpose eq484 eq484
  have eq661 (X0 : G) : sK0 ≠ X0 := superpose eq656 eq8
  subsumption eq661 eq656


@[equational_result]
theorem Equation14609_implies_Equation2 (G : Type*) [Magma G] (h : Equation14609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14613_implies_Equation2 (G : Type*) [Magma G] (h : Equation14613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation14615_implies_Equation2 (G : Type*) [Magma G] (h : Equation14615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation14616_implies_Equation2 (G : Type*) [Magma G] (h : Equation14616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq42 eq34


@[equational_result]
theorem Equation14617_implies_Equation2 (G : Type*) [Magma G] (h : Equation14617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation14618_implies_Equation2 (G : Type*) [Magma G] (h : Equation14618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14620_implies_Equation2 (G : Type*) [Magma G] (h : Equation14620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq9
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq94 eq62


@[equational_result]
theorem Equation14621_implies_Equation2 (G : Type*) [Magma G] (h : Equation14621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X3) ◇ (X0 ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation14622_implies_Equation2 (G : Type*) [Magma G] (h : Equation14622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14624_implies_Equation2 (G : Type*) [Magma G] (h : Equation14624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq14 eq10
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq17
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq18 eq9
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq77 eq54


@[equational_result]
theorem Equation14626_implies_Equation2 (G : Type*) [Magma G] (h : Equation14626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14628_implies_Equation2 (G : Type*) [Magma G] (h : Equation14628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation14629_implies_Equation2 (G : Type*) [Magma G] (h : Equation14629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X3) ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation14630_implies_Equation2 (G : Type*) [Magma G] (h : Equation14630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation14632_implies_Equation2 (G : Type*) [Magma G] (h : Equation14632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X5)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq41 eq32


@[equational_result]
theorem Equation14633_implies_Equation2 (G : Type*) [Magma G] (h : Equation14633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X5)) ◇ (((X0 ◇ X3) ◇ (X0 ◇ X4)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14634_implies_Equation2 (G : Type*) [Magma G] (h : Equation14634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X0 ◇ X4) ◇ (X0 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation14635_implies_Equation2 (G : Type*) [Magma G] (h : Equation14635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14637_implies_Equation2 (G : Type*) [Magma G] (h : Equation14637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X3 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq9 eq9
  have eq42 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq7 eq12
  have eq152 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq42 eq42
  have eq192 (X0 X3 : G) : X0 = X3 := superpose eq9 eq152
  have eq299 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq299 eq192


@[equational_result]
theorem Equation14639_implies_Equation2 (G : Type*) [Magma G] (h : Equation14639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14641_implies_Equation2 (G : Type*) [Magma G] (h : Equation14641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq23 eq13


@[equational_result]
theorem Equation14643_implies_Equation2 (G : Type*) [Magma G] (h : Equation14643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation14647_implies_Equation2 (G : Type*) [Magma G] (h : Equation14647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14649_implies_Equation2 (G : Type*) [Magma G] (h : Equation14649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X5)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation14650_implies_Equation2 (G : Type*) [Magma G] (h : Equation14650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X5)) ◇ (((X0 ◇ X3) ◇ (X2 ◇ X4)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation14651_implies_Equation2 (G : Type*) [Magma G] (h : Equation14651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X5)) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation14652_implies_Equation2 (G : Type*) [Magma G] (h : Equation14652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14655_implies_Equation2 (G : Type*) [Magma G] (h : Equation14655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((((X0 ◇ X3) ◇ (X3 ◇ X0)) ◇ X3) ◇ X2)) ◇ (((X0 ◇ X3) ◇ (X3 ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14656_implies_Equation2 (G : Type*) [Magma G] (h : Equation14656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14660_implies_Equation2 (G : Type*) [Magma G] (h : Equation14660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation14663_implies_Equation2 (G : Type*) [Magma G] (h : Equation14663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ X3) ◇ (((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ X3))) ◇ (((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation14664_implies_Equation2 (G : Type*) [Magma G] (h : Equation14664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation14666_implies_Equation2 (G : Type*) [Magma G] (h : Equation14666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation14667_implies_Equation2 (G : Type*) [Magma G] (h : Equation14667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((((X0 ◇ X3) ◇ (X3 ◇ X4)) ◇ X3) ◇ X5)) ◇ (((X0 ◇ X3) ◇ (X3 ◇ X4)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14668_implies_Equation2 (G : Type*) [Magma G] (h : Equation14668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X0 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq75 eq14


@[equational_result]
theorem Equation14669_implies_Equation2 (G : Type*) [Magma G] (h : Equation14669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation14671_implies_Equation2 (G : Type*) [Magma G] (h : Equation14671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq127 eq45


@[equational_result]
theorem Equation14672_implies_Equation2 (G : Type*) [Magma G] (h : Equation14672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X2)) ◇ (((X0 ◇ X3) ◇ (X4 ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14673_implies_Equation2 (G : Type*) [Magma G] (h : Equation14673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14674_implies_Equation2 (G : Type*) [Magma G] (h : Equation14674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14676_implies_Equation2 (G : Type*) [Magma G] (h : Equation14676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X1)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation14677_implies_Equation2 (G : Type*) [Magma G] (h : Equation14677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation14678_implies_Equation2 (G : Type*) [Magma G] (h : Equation14678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X1)) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation14679_implies_Equation2 (G : Type*) [Magma G] (h : Equation14679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14681_implies_Equation2 (G : Type*) [Magma G] (h : Equation14681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X3) ◇ (X4 ◇ X3)) ◇ X2))) ◇ X1)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq141 eq50


@[equational_result]
theorem Equation14682_implies_Equation2 (G : Type*) [Magma G] (h : Equation14682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X3) ◇ (X4 ◇ X3)) ◇ X3))) ◇ (((X0 ◇ X3) ◇ (X4 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14683_implies_Equation2 (G : Type*) [Magma G] (h : Equation14683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation14684_implies_Equation2 (G : Type*) [Magma G] (h : Equation14684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation14686_implies_Equation2 (G : Type*) [Magma G] (h : Equation14686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X5)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) = X0 := superpose eq7 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq7
  have eq33 (X1 X2 X5 : G) : (X1 ◇ ((X5 ◇ X5) ◇ X1)) = X2 := superpose eq31 eq9
  have eq39 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq31 eq33
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq31 eq39
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq47 eq42


@[equational_result]
theorem Equation14687_implies_Equation2 (G : Type*) [Magma G] (h : Equation14687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (((X0 ◇ X3) ◇ (X4 ◇ X4)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation14688_implies_Equation2 (G : Type*) [Magma G] (h : Equation14688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X0 ◇ X4) ◇ (X5 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation14689_implies_Equation2 (G : Type*) [Magma G] (h : Equation14689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14691_implies_Equation2 (G : Type*) [Magma G] (h : Equation14691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation14692_implies_Equation2 (G : Type*) [Magma G] (h : Equation14692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X0 ◇ (X6 ◇ X7)) ◇ (((X0 ◇ X3) ◇ (X4 ◇ X5)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14693_implies_Equation2 (G : Type*) [Magma G] (h : Equation14693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14694_implies_Equation2 (G : Type*) [Magma G] (h : Equation14694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X0 ◇ X5) ◇ (X6 ◇ X7)) ◇ X7))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation14695_implies_Equation2 (G : Type*) [Magma G] (h : Equation14695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14698_implies_Equation2 (G : Type*) [Magma G] (h : Equation14698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation14701_implies_Equation2 (G : Type*) [Magma G] (h : Equation14701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation14703_implies_Equation2 (G : Type*) [Magma G] (h : Equation14703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq137 eq37


@[equational_result]
theorem Equation14704_implies_Equation2 (G : Type*) [Magma G] (h : Equation14704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = (X1 ◇ ((X0 ◇ X3) ◇ ((((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X4))) := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X0 ◇ X4)) ◇ X4)))) = X2 := superpose eq7 eq10
  have eq142 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X2) ◇ (X2 ◇ X4)) ◇ X4)) = (X0 ◇ (((X1 ◇ X2) ◇ X5) ◇ ((((((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ (((((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X2) ◇ (X2 ◇ X4)) ◇ X4)) ◇ X5) ◇ (X5 ◇ X6)) ◇ X6))) := superpose eq11 eq11
  have eq185 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X5) ◇ (((X2 ◇ X5) ◇ (X5 ◇ X6)) ◇ X6))) = X2 := superpose eq7 eq142
  have eq211 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq185 eq17
  have eq261 (X0 X3 : G) : X0 = X3 := superpose eq7 eq211
  have eq331 (X0 : G) : sK0 ≠ X0 := superpose eq261 eq8
  subsumption eq331 eq261


@[equational_result]
theorem Equation14705_implies_Equation2 (G : Type*) [Magma G] (h : Equation14705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14708_implies_Equation2 (G : Type*) [Magma G] (h : Equation14708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq57 eq11


@[equational_result]
theorem Equation14711_implies_Equation2 (G : Type*) [Magma G] (h : Equation14711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq65 eq11


@[equational_result]
theorem Equation14713_implies_Equation2 (G : Type*) [Magma G] (h : Equation14713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq123 eq57


@[equational_result]
theorem Equation14715_implies_Equation2 (G : Type*) [Magma G] (h : Equation14715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14717_implies_Equation2 (G : Type*) [Magma G] (h : Equation14717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1))) ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq9
  have eq18 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq15 eq7
  have eq31 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) := superpose eq15 eq15
  have eq75 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ X2) := superpose eq15 eq31
  have eq93 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (((X2 ◇ X0) ◇ X1) ◇ X2) := superpose eq18 eq75
  have eq146 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq18 eq93
  have eq230 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) = X2 := superpose eq146 eq18
  have eq278 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq18 eq230
  have eq302 (X0 X2 : G) : X0 = X2 := superpose eq18 eq278
  have eq474 (X0 : G) : sK0 ≠ X0 := superpose eq302 eq8
  subsumption eq474 eq302


@[equational_result]
theorem Equation14719_implies_Equation2 (G : Type*) [Magma G] (h : Equation14719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14721_implies_Equation2 (G : Type*) [Magma G] (h : Equation14721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) = (X1 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ ((((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1))) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X1) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1)) = ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1))) := superpose eq10 eq10
  have eq53 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)))) = X3 := superpose eq34 eq10
  have eq71 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq25
  have eq76 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq25 eq25
  have eq89 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X0)) = ((((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X3) ◇ ((((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X3)))) := superpose eq9 eq53
  have eq125 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1)) = ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1)) := superpose eq53 eq76
  have eq147 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X0)) = ((((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X3) ◇ ((((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X3) ◇ ((X0 ◇ X0) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X3)))) := superpose eq125 eq89
  have eq150 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X0)) = X0 := superpose eq53 eq147
  have eq151 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq150 eq7
  have eq173 (X0 X1 X2 X4 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X4 ◇ X0)) ◇ X0) = X0 := superpose eq150 eq71
  have eq243 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq150 eq173
  have eq244 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq243 eq151
  have eq257 (X0 X2 : G) : X0 = X2 := superpose eq244 eq244
  have eq259 (X0 : G) : sK0 ≠ X0 := superpose eq257 eq8
  subsumption eq259 eq257


@[equational_result]
theorem Equation14723_implies_Equation2 (G : Type*) [Magma G] (h : Equation14723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14727_implies_Equation2 (G : Type*) [Magma G] (h : Equation14727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation14729_implies_Equation2 (G : Type*) [Magma G] (h : Equation14729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation14730_implies_Equation2 (G : Type*) [Magma G] (h : Equation14730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation14731_implies_Equation2 (G : Type*) [Magma G] (h : Equation14731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq79 eq15


@[equational_result]
theorem Equation14732_implies_Equation2 (G : Type*) [Magma G] (h : Equation14732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14735_implies_Equation2 (G : Type*) [Magma G] (h : Equation14735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq54 eq11


@[equational_result]
theorem Equation14738_implies_Equation2 (G : Type*) [Magma G] (h : Equation14738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation14740_implies_Equation2 (G : Type*) [Magma G] (h : Equation14740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation14742_implies_Equation2 (G : Type*) [Magma G] (h : Equation14742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation14745_implies_Equation2 (G : Type*) [Magma G] (h : Equation14745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq65 eq11


@[equational_result]
theorem Equation14747_implies_Equation2 (G : Type*) [Magma G] (h : Equation14747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation14748_implies_Equation2 (G : Type*) [Magma G] (h : Equation14748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14750_implies_Equation2 (G : Type*) [Magma G] (h : Equation14750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14751_implies_Equation2 (G : Type*) [Magma G] (h : Equation14751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14752_implies_Equation2 (G : Type*) [Magma G] (h : Equation14752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14754_implies_Equation2 (G : Type*) [Magma G] (h : Equation14754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation14756_implies_Equation2 (G : Type*) [Magma G] (h : Equation14756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation14758_implies_Equation2 (G : Type*) [Magma G] (h : Equation14758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14759_implies_Equation2 (G : Type*) [Magma G] (h : Equation14759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14760_implies_Equation2 (G : Type*) [Magma G] (h : Equation14760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14762_implies_Equation2 (G : Type*) [Magma G] (h : Equation14762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14763_implies_Equation2 (G : Type*) [Magma G] (h : Equation14763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14764_implies_Equation2 (G : Type*) [Magma G] (h : Equation14764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14766_implies_Equation2 (G : Type*) [Magma G] (h : Equation14766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14767_implies_Equation2 (G : Type*) [Magma G] (h : Equation14767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14768_implies_Equation2 (G : Type*) [Magma G] (h : Equation14768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14769_implies_Equation2 (G : Type*) [Magma G] (h : Equation14769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14771_implies_Equation2 (G : Type*) [Magma G] (h : Equation14771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq9 eq9
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq7 eq12
  have eq115 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq97 eq7
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq9 eq115
  have eq212 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq212 eq119


@[equational_result]
theorem Equation14773_implies_Equation2 (G : Type*) [Magma G] (h : Equation14773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14775_implies_Equation2 (G : Type*) [Magma G] (h : Equation14775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq9 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq9 eq14
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq20 eq12
  have eq41 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq31 eq31
  have eq44 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = X3 := superpose eq14 eq31
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq41 eq44
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq83 eq73


@[equational_result]
theorem Equation14777_implies_Equation2 (G : Type*) [Magma G] (h : Equation14777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14781_implies_Equation2 (G : Type*) [Magma G] (h : Equation14781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation14783_implies_Equation2 (G : Type*) [Magma G] (h : Equation14783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation14784_implies_Equation2 (G : Type*) [Magma G] (h : Equation14784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation14785_implies_Equation2 (G : Type*) [Magma G] (h : Equation14785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation14786_implies_Equation2 (G : Type*) [Magma G] (h : Equation14786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14788_implies_Equation2 (G : Type*) [Magma G] (h : Equation14788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq7 eq10
  have eq72 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq35 eq9
  have eq118 (X0 X3 : G) : X0 = X3 := superpose eq7 eq72
  have eq264 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq264 eq118


@[equational_result]
theorem Equation14790_implies_Equation2 (G : Type*) [Magma G] (h : Equation14790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14792_implies_Equation2 (G : Type*) [Magma G] (h : Equation14792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14793_implies_Equation2 (G : Type*) [Magma G] (h : Equation14793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14794_implies_Equation2 (G : Type*) [Magma G] (h : Equation14794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14796_implies_Equation2 (G : Type*) [Magma G] (h : Equation14796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14797_implies_Equation2 (G : Type*) [Magma G] (h : Equation14797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14798_implies_Equation2 (G : Type*) [Magma G] (h : Equation14798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14800_implies_Equation2 (G : Type*) [Magma G] (h : Equation14800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14801_implies_Equation2 (G : Type*) [Magma G] (h : Equation14801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14802_implies_Equation2 (G : Type*) [Magma G] (h : Equation14802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14803_implies_Equation2 (G : Type*) [Magma G] (h : Equation14803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14807_implies_Equation2 (G : Type*) [Magma G] (h : Equation14807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation14809_implies_Equation2 (G : Type*) [Magma G] (h : Equation14809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14810_implies_Equation2 (G : Type*) [Magma G] (h : Equation14810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14811_implies_Equation2 (G : Type*) [Magma G] (h : Equation14811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14813_implies_Equation2 (G : Type*) [Magma G] (h : Equation14813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14814_implies_Equation2 (G : Type*) [Magma G] (h : Equation14814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14815_implies_Equation2 (G : Type*) [Magma G] (h : Equation14815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14817_implies_Equation2 (G : Type*) [Magma G] (h : Equation14817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14818_implies_Equation2 (G : Type*) [Magma G] (h : Equation14818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14819_implies_Equation2 (G : Type*) [Magma G] (h : Equation14819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14820_implies_Equation2 (G : Type*) [Magma G] (h : Equation14820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14822_implies_Equation2 (G : Type*) [Magma G] (h : Equation14822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq153 eq49


@[equational_result]
theorem Equation14823_implies_Equation2 (G : Type*) [Magma G] (h : Equation14823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation14824_implies_Equation2 (G : Type*) [Magma G] (h : Equation14824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X4)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq9 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq155 eq41


@[equational_result]
theorem Equation14825_implies_Equation2 (G : Type*) [Magma G] (h : Equation14825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14827_implies_Equation2 (G : Type*) [Magma G] (h : Equation14827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14828_implies_Equation2 (G : Type*) [Magma G] (h : Equation14828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14829_implies_Equation2 (G : Type*) [Magma G] (h : Equation14829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14830_implies_Equation2 (G : Type*) [Magma G] (h : Equation14830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14832_implies_Equation2 (G : Type*) [Magma G] (h : Equation14832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14833_implies_Equation2 (G : Type*) [Magma G] (h : Equation14833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14834_implies_Equation2 (G : Type*) [Magma G] (h : Equation14834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14835_implies_Equation2 (G : Type*) [Magma G] (h : Equation14835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14837_implies_Equation2 (G : Type*) [Magma G] (h : Equation14837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14838_implies_Equation2 (G : Type*) [Magma G] (h : Equation14838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14839_implies_Equation2 (G : Type*) [Magma G] (h : Equation14839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14840_implies_Equation2 (G : Type*) [Magma G] (h : Equation14840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14842_implies_Equation2 (G : Type*) [Magma G] (h : Equation14842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14843_implies_Equation2 (G : Type*) [Magma G] (h : Equation14843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14844_implies_Equation2 (G : Type*) [Magma G] (h : Equation14844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14845_implies_Equation2 (G : Type*) [Magma G] (h : Equation14845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14846_implies_Equation2 (G : Type*) [Magma G] (h : Equation14846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14848_implies_Equation2 (G : Type*) [Magma G] (h : Equation14848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X1)) = X3 := superpose eq10 eq7
  have eq37 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq10 eq19
  have eq108 (X0 X3 : G) : X0 = X3 := superpose eq7 eq37
  have eq209 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq209 eq108


@[equational_result]
theorem Equation14849_implies_Equation2 (G : Type*) [Magma G] (h : Equation14849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq66 eq14


@[equational_result]
theorem Equation14850_implies_Equation2 (G : Type*) [Magma G] (h : Equation14850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation14852_implies_Equation2 (G : Type*) [Magma G] (h : Equation14852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = (X1 ◇ ((X0 ◇ ((((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X3 ◇ X2) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3) = (X4 ◇ (((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3) ◇ X4)) ◇ X4)) := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) = (X4 ◇ ((X2 ◇ ((((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X4)) ◇ X4)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) = ((((X4 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3)) ◇ ((X2 ◇ X0) ◇ (((X4 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3)))) := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3)) ◇ X3) ◇ (((X4 ◇ X3) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3)) ◇ X3))) = X3 := superpose eq9 eq7
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X4)) ◇ X4) = ((((X3 ◇ X4) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X4)) ◇ X4)) ◇ (((X5 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X4)) ◇ X4)) ◇ X4) ◇ (((X3 ◇ X4) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X4)) ◇ X4)))) := superpose eq9 eq10
  have eq31 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = ((((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ (((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq10 eq9
  have eq63 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6))) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6)) ◇ X6)) ◇ X6) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6))) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6)) ◇ X6)) ◇ X6))) = X6 := superpose eq13 eq10
  have eq75 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X3 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X3 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) := superpose eq31 eq31
  have eq76 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3) = ((((X4 ◇ X3) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3)) ◇ (((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3)))) := superpose eq7 eq31
  have eq79 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X4)) ◇ X4) = ((((X5 ◇ X4) ◇ (((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X4)) ◇ X4)) ◇ (((((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X4) ◇ (((X5 ◇ X4) ◇ (((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X4)) ◇ X4)))) := superpose eq10 eq31
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) = ((((X4 ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2))) ◇ (X0 ◇ (((X4 ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2))))) := superpose eq7 eq31
  have eq85 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) = ((((X5 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X3 ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X5 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X3 ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))))) := superpose eq31 eq31
  have eq90 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = (((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X4 ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) := superpose eq31 eq7
  have eq102 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = (((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) := superpose eq7 eq75
  have eq106 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = (((X3 ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq90 eq102
  have eq154 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) ◇ X3)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) ◇ X3)) ◇ X3))) = X3 := superpose eq7 eq17
  have eq174 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0))) ◇ ((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0) = ((X0 ◇ (((X1 ◇ (((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0))) ◇ ((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0)) ◇ (((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ (((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0))) ◇ ((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0)))) := superpose eq17 eq31
  have eq193 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0))) ◇ ((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0) = ((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ (((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0) ◇ (((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)))) := superpose eq7 eq174
  have eq194 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0) = (((X1 ◇ (((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0))) ◇ ((((X2 ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5)) ◇ ((X4 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X5) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0) := superpose eq29 eq193
  have eq223 (X0 X1 X2 : G) : (((X1 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) = X1 := superpose eq9 eq154
  have eq378 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) = ((((((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) ◇ ((((X5 ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)))) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0))) ◇ (((X5 ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0)) := superpose eq17 eq223
  have eq382 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) = (((((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((((X4 ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X4 ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq31 eq223
  have eq389 (X0 X1 X2 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) ◇ (((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)))) := superpose eq223 eq11
  have eq416 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) = ((((((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) ◇ (((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)))) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0))) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) := superpose eq194 eq378
  have eq417 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) = ((((((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0))) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) := superpose eq17 eq416
  have eq422 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) = (((((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq106 eq382
  have eq423 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) = (((((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq31 eq422
  have eq426 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq10 eq389
  have eq509 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X5) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) = ((((X6 ◇ ((X1 ◇ X5) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X3 ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X5) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X6 ◇ ((X1 ◇ X5) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X3 ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X5) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))))))) := superpose eq15 eq31
  have eq525 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5)) = ((((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5) ◇ (X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5)))) ◇ (X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5))) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5))) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X5)) ◇ X5)) := superpose eq13 eq426
  have eq533 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = ((X2 ◇ ((((X3 ◇ X2) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2)) ◇ X2) := superpose eq7 eq426
  have eq548 (X0 X1 X2 X3 X4 X5 : G) : (((((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0)) ◇ ((((X5 ◇ (((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0))) ◇ ((((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0) ◇ (((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0)))) ◇ (((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0))) = X0 := superpose eq17 eq426
  have eq617 (X0 X1 X2 X3 X4 : G) : (((((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0) ◇ (((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0)))) ◇ (((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0))) = X0 := superpose eq194 eq548
  have eq618 (X0 X1 X2 X3 X4 : G) : (((((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0)) ◇ X0) ◇ (((X4 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) ◇ ((X1 ◇ ((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0)) ◇ X0))) = X0 := superpose eq17 eq617
  have eq619 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) = (X0 ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) := superpose eq618 eq417
  have eq620 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) = (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) ◇ ((X3 ◇ ((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0)) ◇ X0)) := superpose eq9 eq619
  have eq625 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3) = ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq620 eq76
  have eq655 (X0 X1 X2 X3 : G) : (((((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3) ◇ X0) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := superpose eq620 eq618
  have eq672 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) = ((X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) ◇ X3) := superpose eq655 eq625
  have eq674 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = (X1 ◇ ((((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X1)) := superpose eq672 eq9
  have eq797 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = (((X3 ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X4 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) := superpose eq674 eq85
  have eq799 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = (((X3 ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X5) ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) := superpose eq674 eq509
  have eq802 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) = ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq797 eq423
  have eq812 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) = X2 := superpose eq10 eq802
  have eq813 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = ((((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq812 eq31
  have eq833 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) = ((X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) := superpose eq813 eq533
  have eq836 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) := superpose eq7 eq833
  have eq837 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq836 eq7
  have eq860 (X0 X1 X2 X4 X5 X6 : G) : ((((X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6))) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6)) ◇ X6)) ◇ X6) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (((X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6))) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6)) ◇ X6)) ◇ X6))) = X6 := superpose eq836 eq63
  have eq867 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X4)) ◇ X4) = ((((X5 ◇ X4) ◇ (((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X4)) ◇ X4)) ◇ (((((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X4) ◇ (((X5 ◇ X4) ◇ (((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X4)) ◇ X4)))) := superpose eq836 eq79
  have eq868 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = ((((X4 ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (((X4 ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2))))) := superpose eq836 eq81
  have eq935 (X0 X1 X2 X4 X5 : G) : (X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5)) = ((((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5) ◇ (X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5)))) ◇ (X4 ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5))) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5))) ◇ ((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) ◇ X5)) := superpose eq836 eq525
  have eq977 (X0 X1 X2 X5 X6 : G) : ((((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6)) ◇ X6) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6)) ◇ X6))) = X6 := superpose eq836 eq860
  have eq988 (X0 X2 X3 X4 : G) : ((((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X4) = ((X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) ◇ X4)) ◇ X4) := superpose eq837 eq867
  have eq1000 (X0 X1 X2 X5 X6 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6)) ◇ X6) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X5 ◇ X6)) ◇ X6))) = X6 := superpose eq988 eq977
  have eq1003 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq837 eq868
  have eq1011 (X0 X2 X4 : G) : (X2 ◇ X4) = ((X0 ◇ (X2 ◇ X4)) ◇ X4) := superpose eq1003 eq988
  have eq1014 (X2 X5 X6 : G) : (((X2 ◇ (X5 ◇ X6)) ◇ X6) ◇ (X2 ◇ ((X2 ◇ (X5 ◇ X6)) ◇ X6))) = X6 := superpose eq1003 eq1000
  have eq1024 (X2 X5 X6 : G) : ((X5 ◇ X6) ◇ (X2 ◇ (X5 ◇ X6))) = X6 := superpose eq1011 eq1014
  have eq1045 (X0 X1 X2 X4 X5 : G) : (X4 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) = ((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5) ◇ (X4 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)))) ◇ (X4 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X5)) := superpose eq1011 eq935
  have eq1046 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = (((X2 ◇ X5) ◇ (((X2 ◇ ((X2 ◇ X5) ◇ (X4 ◇ (X2 ◇ X5)))) ◇ (X4 ◇ (X2 ◇ X5))) ◇ (X2 ◇ X5))) ◇ (X2 ◇ X5)) := superpose eq1003 eq1045
  have eq1047 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = (X5 ◇ (X2 ◇ X5)) := superpose eq1024 eq1046
  have eq1048 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = X2 := superpose eq837 eq1047
  have eq1113 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = (((X3 ◇ (((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X4 ◇ X5) ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)))) := superpose eq1048 eq799
  have eq1114 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = (((X3 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ X5) := superpose eq1048 eq1113
  have eq1115 (X0 X1 X2 X5 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X5) := superpose eq1048 eq1114
  have eq1116 (X1 X2 X5 : G) : (X1 ◇ X2) = (X1 ◇ X5) := superpose eq1048 eq1115
  have eq1226 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq837 eq1116
  have eq1242 (X0 X2 : G) : X0 = X2 := superpose eq837 eq1226
  have eq1278 (X0 : G) : sK0 ≠ X0 := superpose eq1242 eq8
  subsumption eq1278 eq1242


@[equational_result]
theorem Equation14854_implies_Equation2 (G : Type*) [Magma G] (h : Equation14854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation14857_implies_Equation2 (G : Type*) [Magma G] (h : Equation14857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation14858_implies_Equation2 (G : Type*) [Magma G] (h : Equation14858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation14860_implies_Equation2 (G : Type*) [Magma G] (h : Equation14860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq161 eq67


@[equational_result]
theorem Equation14861_implies_Equation2 (G : Type*) [Magma G] (h : Equation14861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14862_implies_Equation2 (G : Type*) [Magma G] (h : Equation14862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ X0) ◇ (X0 ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation14863_implies_Equation2 (G : Type*) [Magma G] (h : Equation14863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation14865_implies_Equation2 (G : Type*) [Magma G] (h : Equation14865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ (((X3 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = (X2 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq7 eq9
  have eq18 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq15 eq7
  have eq19 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2)))) ◇ X1)) := superpose eq15 eq9
  have eq29 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ X3)) = (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X3 ◇ X0)) ◇ X3) := superpose eq15 eq15
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X2)) = (((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) ◇ X2) := superpose eq18 eq15
  have eq33 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) ◇ X2) = (X2 ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2))) := superpose eq15 eq30
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) ◇ X2) := superpose eq18 eq33
  have eq64 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X0)) ◇ X2) := superpose eq15 eq29
  have eq79 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq18 eq64
  have eq100 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq15 eq79
  have eq108 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ X2) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ X2)) ◇ X2)) = ((X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) := superpose eq19 eq79
  have eq128 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X2 := superpose eq79 eq18
  have eq157 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose eq18 eq100
  have eq200 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq18 eq128
  have eq211 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq18 eq128
  have eq253 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = (X2 ◇ (X2 ◇ (((X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ X2) ◇ X2))) := superpose eq211 eq108
  have eq261 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq200 eq253
  have eq262 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = X2 := superpose eq18 eq261
  have eq270 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq262 eq34
  have eq321 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq270 eq18
  have eq334 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq270 eq211
  have eq379 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq334 eq321
  have eq388 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq379 eq334
  have eq390 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq388 eq157
  have eq397 (X0 X3 : G) : X0 = X3 := superpose eq390 eq390
  have eq399 (X0 : G) : sK0 ≠ X0 := superpose eq397 eq8
  subsumption eq399 eq397


@[equational_result]
theorem Equation14867_implies_Equation2 (G : Type*) [Magma G] (h : Equation14867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14869_implies_Equation2 (G : Type*) [Magma G] (h : Equation14869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X3) = X0 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X4 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ X2)) ◇ X2)) = X4 := superpose eq9 eq7
  have eq26 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq17 eq21
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq58 eq27


@[equational_result]
theorem Equation14871_implies_Equation2 (G : Type*) [Magma G] (h : Equation14871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation14875_implies_Equation2 (G : Type*) [Magma G] (h : Equation14875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14877_implies_Equation2 (G : Type*) [Magma G] (h : Equation14877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq10
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq152 eq68


@[equational_result]
theorem Equation14878_implies_Equation2 (G : Type*) [Magma G] (h : Equation14878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq10 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq45 eq36


@[equational_result]
theorem Equation14879_implies_Equation2 (G : Type*) [Magma G] (h : Equation14879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ (X2 ◇ X4)) ◇ X4) = (X1 ◇ ((X0 ◇ (X1 ◇ X5)) ◇ X5)) := superpose eq7 eq7
  have eq47 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X4) = X0 := superpose eq7 eq9
  have eq53 (X0 X1 X2 X3 X6 X7 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X3 ◇ X7)) ◇ X7)) = X6 := superpose eq9 eq7
  have eq70 (X2 X3 X6 : G) : (X3 ◇ X2) = X6 := superpose eq47 eq53
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq70
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq174 eq71


@[equational_result]
theorem Equation14880_implies_Equation2 (G : Type*) [Magma G] (h : Equation14880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14882_implies_Equation2 (G : Type*) [Magma G] (h : Equation14882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = X0 := superpose eq7 eq9
  have eq39 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X4 ◇ X5) ◇ (X4 ◇ X5))) ◇ X3) = X5 := superpose eq9 eq10
  have eq57 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq22 eq39
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq57
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq146 eq58


@[equational_result]
theorem Equation14883_implies_Equation2 (G : Type*) [Magma G] (h : Equation14883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq39 eq12


@[equational_result]
theorem Equation14884_implies_Equation2 (G : Type*) [Magma G] (h : Equation14884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14888_implies_Equation2 (G : Type*) [Magma G] (h : Equation14888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation14891_implies_Equation2 (G : Type*) [Magma G] (h : Equation14891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation14892_implies_Equation2 (G : Type*) [Magma G] (h : Equation14892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14894_implies_Equation2 (G : Type*) [Magma G] (h : Equation14894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation14895_implies_Equation2 (G : Type*) [Magma G] (h : Equation14895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14896_implies_Equation2 (G : Type*) [Magma G] (h : Equation14896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ X0) ◇ (X4 ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation14897_implies_Equation2 (G : Type*) [Magma G] (h : Equation14897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14899_implies_Equation2 (G : Type*) [Magma G] (h : Equation14899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X5 ◇ (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ X2))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ X5) = (X1 ◇ (((X2 ◇ (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ X5)) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X0) := superpose eq7 eq11
  have eq30 (X0 X1 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ X5) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq23 eq10
  have eq31 (X0 X1 X2 X3 X4 X5 X6 : G) : (X6 ◇ (((((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X1) ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X1)) ◇ X6)) = ((X0 ◇ (X4 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X1))) ◇ X5) := superpose eq7 eq30
  have eq53 (X0 X1 X5 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X5 := superpose eq30 eq11
  have eq75 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X1))) ◇ X5) = X1 := superpose eq7 eq31
  have eq76 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ X2) := superpose eq75 eq9
  have eq150 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq76
  have eq202 (X0 X1 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X5 := superpose eq150 eq53
  have eq246 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq150 eq202
  have eq247 (X0 X3 : G) : X0 = X3 := superpose eq246 eq246
  have eq252 (X0 : G) : sK0 ≠ X0 := superpose eq247 eq8
  subsumption eq252 eq247


@[equational_result]
theorem Equation14900_implies_Equation2 (G : Type*) [Magma G] (h : Equation14900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation14901_implies_Equation2 (G : Type*) [Magma G] (h : Equation14901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation14902_implies_Equation2 (G : Type*) [Magma G] (h : Equation14902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation14904_implies_Equation2 (G : Type*) [Magma G] (h : Equation14904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq40 eq16


@[equational_result]
theorem Equation14905_implies_Equation2 (G : Type*) [Magma G] (h : Equation14905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq77 eq15


@[equational_result]
theorem Equation14906_implies_Equation2 (G : Type*) [Magma G] (h : Equation14906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ (X4 ◇ X2)) ◇ X4) = (X1 ◇ ((X0 ◇ (X5 ◇ X1)) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))))) = X3 := superpose eq7 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ (X4 ◇ X1)) ◇ (X5 ◇ X6)) ◇ X5) = (X7 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) := superpose eq9 eq9
  have eq46 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X3) = X0 := superpose eq7 eq9
  have eq49 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (((X3 ◇ (X4 ◇ X5)) ◇ X6) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)))) = X5 := superpose eq9 eq11
  have eq64 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X1 := superpose eq46 eq45
  have eq67 (X1 X3 X5 : G) : (X3 ◇ X1) = X5 := superpose eq64 eq49
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq67
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq177 eq68


@[equational_result]
theorem Equation14907_implies_Equation2 (G : Type*) [Magma G] (h : Equation14907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14909_implies_Equation2 (G : Type*) [Magma G] (h : Equation14909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X2) = (X1 ◇ ((X0 ◇ (X5 ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X4) ◇ X5) ◇ X0) ◇ X1)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X6 ◇ (((((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X1) ◇ (X7 ◇ X5)) ◇ X6)) = ((X0 ◇ (X4 ◇ X1)) ◇ X5) := superpose eq7 eq9
  have eq54 (X0 X1 X3 X7 : G) : (X1 ◇ (((X0 ◇ X7) ◇ X3) ◇ X1)) = X7 := superpose eq7 eq10
  have eq78 (X0 X1 X4 X5 : G) : ((X0 ◇ (X4 ◇ X1)) ◇ X5) = X1 := superpose eq54 eq12
  have eq82 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq78 eq7
  have eq114 (X0 X3 : G) : X0 = X3 := superpose eq82 eq82
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq116 eq114


@[equational_result]
theorem Equation14910_implies_Equation2 (G : Type*) [Magma G] (h : Equation14910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X2) ◇ X4) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation14911_implies_Equation2 (G : Type*) [Magma G] (h : Equation14911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation14912_implies_Equation2 (G : Type*) [Magma G] (h : Equation14912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14914_implies_Equation2 (G : Type*) [Magma G] (h : Equation14914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq76 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq168 eq76


@[equational_result]
theorem Equation14915_implies_Equation2 (G : Type*) [Magma G] (h : Equation14915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation14916_implies_Equation2 (G : Type*) [Magma G] (h : Equation14916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ X0) ◇ (X5 ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq70 eq13


@[equational_result]
theorem Equation14917_implies_Equation2 (G : Type*) [Magma G] (h : Equation14917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14919_implies_Equation2 (G : Type*) [Magma G] (h : Equation14919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation14920_implies_Equation2 (G : Type*) [Magma G] (h : Equation14920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14921_implies_Equation2 (G : Type*) [Magma G] (h : Equation14921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14922_implies_Equation2 (G : Type*) [Magma G] (h : Equation14922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X5 ◇ X0) ◇ (X6 ◇ X7)) ◇ X7))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation14923_implies_Equation2 (G : Type*) [Magma G] (h : Equation14923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14925_implies_Equation2 (G : Type*) [Magma G] (h : Equation14925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq9
  have eq20 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X1)) = X3 := superpose eq12 eq7
  have eq23 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq12 eq20
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq166 eq60


@[equational_result]
theorem Equation14927_implies_Equation2 (G : Type*) [Magma G] (h : Equation14927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq63 eq12


@[equational_result]
theorem Equation14929_implies_Equation2 (G : Type*) [Magma G] (h : Equation14929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3) = (((X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3))) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3)) ◇ (((X4 ◇ ((X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3))) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3))) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3)))) := superpose eq9 eq7
  have eq37 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq66 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq37 eq7
  have eq79 (X0 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq66
  have eq111 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq79 eq79
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq79 eq10
  have eq116 (X0 X2 : G) : (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) = X2 := superpose eq79 eq9
  have eq117 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq79 eq7
  have eq124 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)))) := superpose eq79 eq11
  have eq175 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) = (((X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X3 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)))) := superpose eq117 eq16
  have eq232 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq79 eq116
  have eq234 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq116
  have eq238 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq10 eq116
  have eq239 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq11 eq116
  have eq258 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq117 eq232
  have eq344 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X3 ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)))) := superpose eq234 eq175
  have eq397 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X3 ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)))) := superpose eq234 eq344
  have eq398 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X3 ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)))) := superpose eq116 eq397
  have eq419 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq234 eq238
  have eq420 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) := superpose eq116 eq419
  have eq464 (X0 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq234 eq239
  have eq465 (X0 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) := superpose eq116 eq464
  have eq469 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) := superpose eq465 eq420
  have eq567 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq111 eq116
  have eq569 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq234 eq567
  have eq571 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq569 eq258
  have eq613 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq111 eq115
  have eq615 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq117 eq115
  have eq632 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq234 eq613
  have eq633 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq615 eq111
  have eq636 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq615 eq571
  have eq638 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq615 eq632
  have eq639 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq615 eq633
  have eq642 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq615 eq636
  have eq643 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq639 eq638
  have eq644 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq117 eq643
  have eq651 (X0 X2 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq644 eq124
  have eq683 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = X2 := superpose eq644 eq469
  have eq718 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq644 eq642
  have eq719 (X0 X2 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq644 eq651
  have eq753 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (((X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) := superpose eq718 eq398
  have eq754 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) := superpose eq683 eq753
  have eq755 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = X1 := superpose eq719 eq754
  have eq757 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq755 eq116
  have eq896 (X0 X2 : G) : X0 = X2 := superpose eq757 eq757
  have eq898 (X0 : G) : sK0 ≠ X0 := superpose eq896 eq8
  subsumption eq898 eq896


@[equational_result]
theorem Equation14931_implies_Equation2 (G : Type*) [Magma G] (h : Equation14931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation14935_implies_Equation2 (G : Type*) [Magma G] (h : Equation14935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation14937_implies_Equation2 (G : Type*) [Magma G] (h : Equation14937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq76 eq19


@[equational_result]
theorem Equation14938_implies_Equation2 (G : Type*) [Magma G] (h : Equation14938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation14939_implies_Equation2 (G : Type*) [Magma G] (h : Equation14939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X4)) = (X1 ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = (X3 ◇ X0) := superpose eq7 eq11
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X0 := superpose eq16 eq7
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation14940_implies_Equation2 (G : Type*) [Magma G] (h : Equation14940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14942_implies_Equation2 (G : Type*) [Magma G] (h : Equation14942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X0 ◇ ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2) = X0 := superpose eq7 eq10
  have eq34 (X0 X1 X2 X3 : G) : ((X3 ◇ ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2)) = ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2))) := superpose eq9 eq9
  have eq53 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2)))) = X3 := superpose eq34 eq9
  have eq73 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) = X3 := superpose eq25 eq25
  have eq89 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ X1) ◇ X2) ◇ X1) = ((((X3 ◇ X4) ◇ (X4 ◇ X1)) ◇ X4) ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X1)) ◇ X4) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X1)) ◇ X4)))) := superpose eq10 eq53
  have eq126 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X3)) = ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X3)) := superpose eq53 eq73
  have eq146 (X1 X2 X3 X4 X5 : G) : (((X5 ◇ X1) ◇ X2) ◇ X1) = ((((X3 ◇ X4) ◇ (X4 ◇ X1)) ◇ X4) ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X1)) ◇ X4) ◇ ((X1 ◇ X1) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X1)) ◇ X4)))) := superpose eq126 eq89
  have eq147 (X1 X2 X5 : G) : (((X5 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq53 eq146
  have eq148 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq147 eq7
  have eq319 (X0 X2 : G) : X0 = X2 := superpose eq148 eq148
  have eq321 (X0 : G) : sK0 ≠ X0 := superpose eq319 eq8
  subsumption eq321 eq319


@[equational_result]
theorem Equation14944_implies_Equation2 (G : Type*) [Magma G] (h : Equation14944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation14946_implies_Equation2 (G : Type*) [Magma G] (h : Equation14946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14947_implies_Equation2 (G : Type*) [Magma G] (h : Equation14947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14948_implies_Equation2 (G : Type*) [Magma G] (h : Equation14948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14950_implies_Equation2 (G : Type*) [Magma G] (h : Equation14950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14951_implies_Equation2 (G : Type*) [Magma G] (h : Equation14951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14952_implies_Equation2 (G : Type*) [Magma G] (h : Equation14952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14954_implies_Equation2 (G : Type*) [Magma G] (h : Equation14954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14955_implies_Equation2 (G : Type*) [Magma G] (h : Equation14955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14956_implies_Equation2 (G : Type*) [Magma G] (h : Equation14956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14957_implies_Equation2 (G : Type*) [Magma G] (h : Equation14957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14961_implies_Equation2 (G : Type*) [Magma G] (h : Equation14961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation14963_implies_Equation2 (G : Type*) [Magma G] (h : Equation14963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14964_implies_Equation2 (G : Type*) [Magma G] (h : Equation14964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14965_implies_Equation2 (G : Type*) [Magma G] (h : Equation14965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14967_implies_Equation2 (G : Type*) [Magma G] (h : Equation14967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14968_implies_Equation2 (G : Type*) [Magma G] (h : Equation14968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14969_implies_Equation2 (G : Type*) [Magma G] (h : Equation14969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14971_implies_Equation2 (G : Type*) [Magma G] (h : Equation14971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14972_implies_Equation2 (G : Type*) [Magma G] (h : Equation14972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14973_implies_Equation2 (G : Type*) [Magma G] (h : Equation14973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14974_implies_Equation2 (G : Type*) [Magma G] (h : Equation14974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14976_implies_Equation2 (G : Type*) [Magma G] (h : Equation14976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq177 eq71


@[equational_result]
theorem Equation14977_implies_Equation2 (G : Type*) [Magma G] (h : Equation14977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq63 eq15


@[equational_result]
theorem Equation14978_implies_Equation2 (G : Type*) [Magma G] (h : Equation14978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq20 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq7 eq11
  have eq57 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq171 eq57


@[equational_result]
theorem Equation14979_implies_Equation2 (G : Type*) [Magma G] (h : Equation14979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14981_implies_Equation2 (G : Type*) [Magma G] (h : Equation14981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14982_implies_Equation2 (G : Type*) [Magma G] (h : Equation14982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14983_implies_Equation2 (G : Type*) [Magma G] (h : Equation14983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14984_implies_Equation2 (G : Type*) [Magma G] (h : Equation14984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14986_implies_Equation2 (G : Type*) [Magma G] (h : Equation14986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14987_implies_Equation2 (G : Type*) [Magma G] (h : Equation14987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14988_implies_Equation2 (G : Type*) [Magma G] (h : Equation14988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14989_implies_Equation2 (G : Type*) [Magma G] (h : Equation14989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14991_implies_Equation2 (G : Type*) [Magma G] (h : Equation14991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14992_implies_Equation2 (G : Type*) [Magma G] (h : Equation14992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14993_implies_Equation2 (G : Type*) [Magma G] (h : Equation14993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14994_implies_Equation2 (G : Type*) [Magma G] (h : Equation14994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14996_implies_Equation2 (G : Type*) [Magma G] (h : Equation14996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14997_implies_Equation2 (G : Type*) [Magma G] (h : Equation14997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14998_implies_Equation2 (G : Type*) [Magma G] (h : Equation14998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14999_implies_Equation2 (G : Type*) [Magma G] (h : Equation14999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15000_implies_Equation2 (G : Type*) [Magma G] (h : Equation15000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15002_implies_Equation2 (G : Type*) [Magma G] (h : Equation15002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq33 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq9 eq10
  have eq34 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq7 eq10
  have eq37 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq10 eq7
  have eq39 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq37 eq33
  have eq42 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose eq39 eq7
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq39 eq34
  have eq63 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq39 eq42
  have eq100 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq60 eq63
  have eq107 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq60 eq100
  have eq112 (X0 X2 : G) : X0 = X2 := superpose eq107 eq107
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq114 eq112


@[equational_result]
theorem Equation15003_implies_Equation2 (G : Type*) [Magma G] (h : Equation15003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation15004_implies_Equation2 (G : Type*) [Magma G] (h : Equation15004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15008_implies_Equation2 (G : Type*) [Magma G] (h : Equation15008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation15011_implies_Equation2 (G : Type*) [Magma G] (h : Equation15011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2))) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15012_implies_Equation2 (G : Type*) [Magma G] (h : Equation15012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation15014_implies_Equation2 (G : Type*) [Magma G] (h : Equation15014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation15015_implies_Equation2 (G : Type*) [Magma G] (h : Equation15015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15016_implies_Equation2 (G : Type*) [Magma G] (h : Equation15016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X4 ◇ X4) ◇ (X0 ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation15017_implies_Equation2 (G : Type*) [Magma G] (h : Equation15017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15021_implies_Equation2 (G : Type*) [Magma G] (h : Equation15021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq63 eq12


@[equational_result]
theorem Equation15023_implies_Equation2 (G : Type*) [Magma G] (h : Equation15023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15024_implies_Equation2 (G : Type*) [Magma G] (h : Equation15024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15025_implies_Equation2 (G : Type*) [Magma G] (h : Equation15025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15027_implies_Equation2 (G : Type*) [Magma G] (h : Equation15027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15028_implies_Equation2 (G : Type*) [Magma G] (h : Equation15028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15029_implies_Equation2 (G : Type*) [Magma G] (h : Equation15029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15031_implies_Equation2 (G : Type*) [Magma G] (h : Equation15031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15032_implies_Equation2 (G : Type*) [Magma G] (h : Equation15032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15033_implies_Equation2 (G : Type*) [Magma G] (h : Equation15033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15034_implies_Equation2 (G : Type*) [Magma G] (h : Equation15034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15037_implies_Equation2 (G : Type*) [Magma G] (h : Equation15037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15038_implies_Equation2 (G : Type*) [Magma G] (h : Equation15038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15040_implies_Equation2 (G : Type*) [Magma G] (h : Equation15040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15041_implies_Equation2 (G : Type*) [Magma G] (h : Equation15041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15042_implies_Equation2 (G : Type*) [Magma G] (h : Equation15042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15044_implies_Equation2 (G : Type*) [Magma G] (h : Equation15044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15045_implies_Equation2 (G : Type*) [Magma G] (h : Equation15045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15046_implies_Equation2 (G : Type*) [Magma G] (h : Equation15046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15048_implies_Equation2 (G : Type*) [Magma G] (h : Equation15048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15049_implies_Equation2 (G : Type*) [Magma G] (h : Equation15049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15050_implies_Equation2 (G : Type*) [Magma G] (h : Equation15050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15051_implies_Equation2 (G : Type*) [Magma G] (h : Equation15051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15053_implies_Equation2 (G : Type*) [Magma G] (h : Equation15053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq75 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq167 eq75


@[equational_result]
theorem Equation15054_implies_Equation2 (G : Type*) [Magma G] (h : Equation15054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15055_implies_Equation2 (G : Type*) [Magma G] (h : Equation15055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15056_implies_Equation2 (G : Type*) [Magma G] (h : Equation15056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15058_implies_Equation2 (G : Type*) [Magma G] (h : Equation15058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15059_implies_Equation2 (G : Type*) [Magma G] (h : Equation15059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15060_implies_Equation2 (G : Type*) [Magma G] (h : Equation15060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15061_implies_Equation2 (G : Type*) [Magma G] (h : Equation15061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15063_implies_Equation2 (G : Type*) [Magma G] (h : Equation15063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15064_implies_Equation2 (G : Type*) [Magma G] (h : Equation15064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15065_implies_Equation2 (G : Type*) [Magma G] (h : Equation15065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15066_implies_Equation2 (G : Type*) [Magma G] (h : Equation15066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15068_implies_Equation2 (G : Type*) [Magma G] (h : Equation15068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15069_implies_Equation2 (G : Type*) [Magma G] (h : Equation15069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15070_implies_Equation2 (G : Type*) [Magma G] (h : Equation15070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15071_implies_Equation2 (G : Type*) [Magma G] (h : Equation15071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15073_implies_Equation2 (G : Type*) [Magma G] (h : Equation15073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15074_implies_Equation2 (G : Type*) [Magma G] (h : Equation15074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15075_implies_Equation2 (G : Type*) [Magma G] (h : Equation15075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15076_implies_Equation2 (G : Type*) [Magma G] (h : Equation15076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15077_implies_Equation2 (G : Type*) [Magma G] (h : Equation15077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15079_implies_Equation2 (G : Type*) [Magma G] (h : Equation15079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X5))) ◇ X0) = X5 := superpose eq7 eq7
  have eq135 (X0 X5 : G) : (X0 ◇ (X0 ◇ X0)) = X5 := superpose eq11 eq11
  have eq193 (X0 X2 : G) : X0 = X2 := superpose eq135 eq135
  have eq248 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq248 eq193


@[equational_result]
theorem Equation15080_implies_Equation2 (G : Type*) [Magma G] (h : Equation15080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation15081_implies_Equation2 (G : Type*) [Magma G] (h : Equation15081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X0)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation15082_implies_Equation2 (G : Type*) [Magma G] (h : Equation15082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15084_implies_Equation2 (G : Type*) [Magma G] (h : Equation15084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X1)) ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq31 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ (X0 ◇ (X5 ◇ X6))) ◇ (X5 ◇ X6))) = X0 := superpose eq7 eq11
  have eq48 (X0 X1 X2 X5 X6 : G) : ((X1 ◇ X2) ◇ (X6 ◇ (X5 ◇ X6))) = X0 := superpose eq15 eq31
  have eq117 (X0 X5 : G) : X0 = X5 := superpose eq48 eq48
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq155 eq117


@[equational_result]
theorem Equation15085_implies_Equation2 (G : Type*) [Magma G] (h : Equation15085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X1)) ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq125 eq41


@[equational_result]
theorem Equation15086_implies_Equation2 (G : Type*) [Magma G] (h : Equation15086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X1)) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X2)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 X6 X7 : G) : ((X1 ◇ (X4 ◇ X2)) ◇ (X5 ◇ X7)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X6 ◇ X7))) := superpose eq11 eq11
  have eq24 (X1 X2 X4 X5 X7 : G) : ((X1 ◇ (X4 ◇ X2)) ◇ (X5 ◇ X7)) = ((X1 ◇ X2) ◇ (X5 ◇ X7)) := superpose eq11 eq13
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X2)) ◇ X4))) = X5 := superpose eq24 eq9
  have eq52 (X0 X6 : G) : X0 = X6 := superpose eq25 eq25
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq82 eq52


@[equational_result]
theorem Equation15087_implies_Equation2 (G : Type*) [Magma G] (h : Equation15087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15089_implies_Equation2 (G : Type*) [Magma G] (h : Equation15089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X2)) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X4) ◇ X5) ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation15090_implies_Equation2 (G : Type*) [Magma G] (h : Equation15090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X2) ◇ X4) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation15091_implies_Equation2 (G : Type*) [Magma G] (h : Equation15091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ X2)) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X3)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15092_implies_Equation2 (G : Type*) [Magma G] (h : Equation15092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15094_implies_Equation2 (G : Type*) [Magma G] (h : Equation15094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ (((X3 ◇ X4) ◇ (X0 ◇ X4)) ◇ X2))) ◇ X1)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq141 eq50


@[equational_result]
theorem Equation15095_implies_Equation2 (G : Type*) [Magma G] (h : Equation15095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation15096_implies_Equation2 (G : Type*) [Magma G] (h : Equation15096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X5 ◇ (((X3 ◇ X4) ◇ (X0 ◇ X4)) ◇ X4))) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X4)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15097_implies_Equation2 (G : Type*) [Magma G] (h : Equation15097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation15099_implies_Equation2 (G : Type*) [Magma G] (h : Equation15099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation15100_implies_Equation2 (G : Type*) [Magma G] (h : Equation15100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15101_implies_Equation2 (G : Type*) [Magma G] (h : Equation15101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X0 ◇ (X6 ◇ X7)) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X4))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15102_implies_Equation2 (G : Type*) [Magma G] (h : Equation15102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X5 ◇ X6) ◇ (X0 ◇ X7)) ◇ X7))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation15103_implies_Equation2 (G : Type*) [Magma G] (h : Equation15103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15105_implies_Equation2 (G : Type*) [Magma G] (h : Equation15105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq44 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X3) = X0 := superpose eq7 eq10
  have eq75 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq44 eq44
  have eq129 (X0 X4 : G) : X0 = X4 := superpose eq7 eq75
  have eq246 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq246 eq129


@[equational_result]
theorem Equation15106_implies_Equation2 (G : Type*) [Magma G] (h : Equation15106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X5)) ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq160 eq43


@[equational_result]
theorem Equation15107_implies_Equation2 (G : Type*) [Magma G] (h : Equation15107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X5)) ◇ (((X3 ◇ X4) ◇ (X2 ◇ X0)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq43 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq43
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq182 eq52


@[equational_result]
theorem Equation15108_implies_Equation2 (G : Type*) [Magma G] (h : Equation15108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15110_implies_Equation2 (G : Type*) [Magma G] (h : Equation15110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15111_implies_Equation2 (G : Type*) [Magma G] (h : Equation15111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15112_implies_Equation2 (G : Type*) [Magma G] (h : Equation15112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15113_implies_Equation2 (G : Type*) [Magma G] (h : Equation15113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15115_implies_Equation2 (G : Type*) [Magma G] (h : Equation15115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15116_implies_Equation2 (G : Type*) [Magma G] (h : Equation15116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15117_implies_Equation2 (G : Type*) [Magma G] (h : Equation15117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15118_implies_Equation2 (G : Type*) [Magma G] (h : Equation15118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15120_implies_Equation2 (G : Type*) [Magma G] (h : Equation15120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15121_implies_Equation2 (G : Type*) [Magma G] (h : Equation15121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15122_implies_Equation2 (G : Type*) [Magma G] (h : Equation15122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15123_implies_Equation2 (G : Type*) [Magma G] (h : Equation15123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15125_implies_Equation2 (G : Type*) [Magma G] (h : Equation15125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15126_implies_Equation2 (G : Type*) [Magma G] (h : Equation15126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15127_implies_Equation2 (G : Type*) [Magma G] (h : Equation15127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15128_implies_Equation2 (G : Type*) [Magma G] (h : Equation15128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15129_implies_Equation2 (G : Type*) [Magma G] (h : Equation15129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15131_implies_Equation2 (G : Type*) [Magma G] (h : Equation15131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X5)) ◇ X1)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq206 eq72


@[equational_result]
theorem Equation15132_implies_Equation2 (G : Type*) [Magma G] (h : Equation15132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15133_implies_Equation2 (G : Type*) [Magma G] (h : Equation15133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X5)) ◇ (((X3 ◇ X4) ◇ (X3 ◇ X0)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15134_implies_Equation2 (G : Type*) [Magma G] (h : Equation15134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15136_implies_Equation2 (G : Type*) [Magma G] (h : Equation15136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15137_implies_Equation2 (G : Type*) [Magma G] (h : Equation15137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15138_implies_Equation2 (G : Type*) [Magma G] (h : Equation15138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15139_implies_Equation2 (G : Type*) [Magma G] (h : Equation15139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15141_implies_Equation2 (G : Type*) [Magma G] (h : Equation15141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15142_implies_Equation2 (G : Type*) [Magma G] (h : Equation15142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15143_implies_Equation2 (G : Type*) [Magma G] (h : Equation15143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15144_implies_Equation2 (G : Type*) [Magma G] (h : Equation15144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15146_implies_Equation2 (G : Type*) [Magma G] (h : Equation15146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15147_implies_Equation2 (G : Type*) [Magma G] (h : Equation15147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15148_implies_Equation2 (G : Type*) [Magma G] (h : Equation15148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15149_implies_Equation2 (G : Type*) [Magma G] (h : Equation15149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15151_implies_Equation2 (G : Type*) [Magma G] (h : Equation15151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15152_implies_Equation2 (G : Type*) [Magma G] (h : Equation15152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15153_implies_Equation2 (G : Type*) [Magma G] (h : Equation15153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15154_implies_Equation2 (G : Type*) [Magma G] (h : Equation15154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15155_implies_Equation2 (G : Type*) [Magma G] (h : Equation15155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15157_implies_Equation2 (G : Type*) [Magma G] (h : Equation15157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X0))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = X0 := superpose eq7 eq11
  have eq88 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq237 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq237 eq88


@[equational_result]
theorem Equation15158_implies_Equation2 (G : Type*) [Magma G] (h : Equation15158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15159_implies_Equation2 (G : Type*) [Magma G] (h : Equation15159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((((X3 ◇ X4) ◇ (X4 ◇ X0)) ◇ X4) ◇ X5)) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X0)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15160_implies_Equation2 (G : Type*) [Magma G] (h : Equation15160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15162_implies_Equation2 (G : Type*) [Magma G] (h : Equation15162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15163_implies_Equation2 (G : Type*) [Magma G] (h : Equation15163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15164_implies_Equation2 (G : Type*) [Magma G] (h : Equation15164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15165_implies_Equation2 (G : Type*) [Magma G] (h : Equation15165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15167_implies_Equation2 (G : Type*) [Magma G] (h : Equation15167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15168_implies_Equation2 (G : Type*) [Magma G] (h : Equation15168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15169_implies_Equation2 (G : Type*) [Magma G] (h : Equation15169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15170_implies_Equation2 (G : Type*) [Magma G] (h : Equation15170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15172_implies_Equation2 (G : Type*) [Magma G] (h : Equation15172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15173_implies_Equation2 (G : Type*) [Magma G] (h : Equation15173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15174_implies_Equation2 (G : Type*) [Magma G] (h : Equation15174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15175_implies_Equation2 (G : Type*) [Magma G] (h : Equation15175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15177_implies_Equation2 (G : Type*) [Magma G] (h : Equation15177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15178_implies_Equation2 (G : Type*) [Magma G] (h : Equation15178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15179_implies_Equation2 (G : Type*) [Magma G] (h : Equation15179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15180_implies_Equation2 (G : Type*) [Magma G] (h : Equation15180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15181_implies_Equation2 (G : Type*) [Magma G] (h : Equation15181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15183_implies_Equation2 (G : Type*) [Magma G] (h : Equation15183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq173 eq53


@[equational_result]
theorem Equation15184_implies_Equation2 (G : Type*) [Magma G] (h : Equation15184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15185_implies_Equation2 (G : Type*) [Magma G] (h : Equation15185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X0 ◇ (X6 ◇ X7)) ◇ (((X3 ◇ X4) ◇ (X5 ◇ X0)) ◇ X4))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15186_implies_Equation2 (G : Type*) [Magma G] (h : Equation15186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15187_implies_Equation2 (G : Type*) [Magma G] (h : Equation15187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X0)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15189_implies_Equation2 (G : Type*) [Magma G] (h : Equation15189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15190_implies_Equation2 (G : Type*) [Magma G] (h : Equation15190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15191_implies_Equation2 (G : Type*) [Magma G] (h : Equation15191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15192_implies_Equation2 (G : Type*) [Magma G] (h : Equation15192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15193_implies_Equation2 (G : Type*) [Magma G] (h : Equation15193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X1)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15195_implies_Equation2 (G : Type*) [Magma G] (h : Equation15195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15196_implies_Equation2 (G : Type*) [Magma G] (h : Equation15196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15197_implies_Equation2 (G : Type*) [Magma G] (h : Equation15197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15198_implies_Equation2 (G : Type*) [Magma G] (h : Equation15198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15199_implies_Equation2 (G : Type*) [Magma G] (h : Equation15199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X2)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15201_implies_Equation2 (G : Type*) [Magma G] (h : Equation15201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15202_implies_Equation2 (G : Type*) [Magma G] (h : Equation15202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15203_implies_Equation2 (G : Type*) [Magma G] (h : Equation15203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15204_implies_Equation2 (G : Type*) [Magma G] (h : Equation15204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15205_implies_Equation2 (G : Type*) [Magma G] (h : Equation15205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15207_implies_Equation2 (G : Type*) [Magma G] (h : Equation15207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15208_implies_Equation2 (G : Type*) [Magma G] (h : Equation15208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15209_implies_Equation2 (G : Type*) [Magma G] (h : Equation15209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15210_implies_Equation2 (G : Type*) [Magma G] (h : Equation15210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15211_implies_Equation2 (G : Type*) [Magma G] (h : Equation15211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15213_implies_Equation2 (G : Type*) [Magma G] (h : Equation15213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15214_implies_Equation2 (G : Type*) [Magma G] (h : Equation15214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15215_implies_Equation2 (G : Type*) [Magma G] (h : Equation15215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15216_implies_Equation2 (G : Type*) [Magma G] (h : Equation15216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15217_implies_Equation2 (G : Type*) [Magma G] (h : Equation15217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15218_implies_Equation2 (G : Type*) [Magma G] (h : Equation15218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15424_implies_Equation2 (G : Type*) [Magma G] (h : Equation15424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation15427_implies_Equation2 (G : Type*) [Magma G] (h : Equation15427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation15429_implies_Equation2 (G : Type*) [Magma G] (h : Equation15429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation15430_implies_Equation2 (G : Type*) [Magma G] (h : Equation15430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation15431_implies_Equation2 (G : Type*) [Magma G] (h : Equation15431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15434_implies_Equation2 (G : Type*) [Magma G] (h : Equation15434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation15437_implies_Equation2 (G : Type*) [Magma G] (h : Equation15437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation15439_implies_Equation2 (G : Type*) [Magma G] (h : Equation15439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq50 eq14


@[equational_result]
theorem Equation15441_implies_Equation2 (G : Type*) [Magma G] (h : Equation15441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation15443_implies_Equation2 (G : Type*) [Magma G] (h : Equation15443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = (X1 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq12 eq10
  have eq20 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq12 eq19
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq20 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq9 eq22
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq37 eq27


@[equational_result]
theorem Equation15444_implies_Equation2 (G : Type*) [Magma G] (h : Equation15444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15445_implies_Equation2 (G : Type*) [Magma G] (h : Equation15445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15447_implies_Equation2 (G : Type*) [Magma G] (h : Equation15447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq9
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq94 eq34


@[equational_result]
theorem Equation15449_implies_Equation2 (G : Type*) [Magma G] (h : Equation15449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation15452_implies_Equation2 (G : Type*) [Magma G] (h : Equation15452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ X3) ◇ X3)) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15453_implies_Equation2 (G : Type*) [Magma G] (h : Equation15453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15455_implies_Equation2 (G : Type*) [Magma G] (h : Equation15455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation15456_implies_Equation2 (G : Type*) [Magma G] (h : Equation15456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15457_implies_Equation2 (G : Type*) [Magma G] (h : Equation15457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X4)) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation15458_implies_Equation2 (G : Type*) [Magma G] (h : Equation15458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15461_implies_Equation2 (G : Type*) [Magma G] (h : Equation15461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation15464_implies_Equation2 (G : Type*) [Magma G] (h : Equation15464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation15466_implies_Equation2 (G : Type*) [Magma G] (h : Equation15466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq52 eq15


@[equational_result]
theorem Equation15468_implies_Equation2 (G : Type*) [Magma G] (h : Equation15468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15471_implies_Equation2 (G : Type*) [Magma G] (h : Equation15471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq45 eq11


@[equational_result]
theorem Equation15474_implies_Equation2 (G : Type*) [Magma G] (h : Equation15474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq42 eq11


@[equational_result]
theorem Equation15476_implies_Equation2 (G : Type*) [Magma G] (h : Equation15476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation15478_implies_Equation2 (G : Type*) [Magma G] (h : Equation15478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation15480_implies_Equation2 (G : Type*) [Magma G] (h : Equation15480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq9 eq9
  have eq62 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq14 eq11
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq7 eq62
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq156 eq72


@[equational_result]
theorem Equation15481_implies_Equation2 (G : Type*) [Magma G] (h : Equation15481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X3)) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq10
  have eq30 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq9
  have eq54 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3))) = X2 := superpose eq30 eq11
  have eq70 (X0 X1 X2 : G) : ((((X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2))) ◇ X0) = X0 := superpose eq30 eq11
  have eq82 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq7 eq70
  have eq94 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq82 eq30
  have eq123 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq94 eq82
  have eq125 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq123 eq94
  have eq131 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq125 eq123
  have eq132 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3))) = X2 := superpose eq131 eq54
  have eq196 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3)) = X2 := superpose eq131 eq132
  have eq197 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X2 := superpose eq131 eq196
  have eq198 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq131 eq197
  have eq199 (X0 X3 : G) : X0 = X3 := superpose eq198 eq198
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq199 eq8
  subsumption eq204 eq199


@[equational_result]
theorem Equation15482_implies_Equation2 (G : Type*) [Magma G] (h : Equation15482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation15484_implies_Equation2 (G : Type*) [Magma G] (h : Equation15484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X1 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq29 eq23


@[equational_result]
theorem Equation15486_implies_Equation2 (G : Type*) [Magma G] (h : Equation15486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation15489_implies_Equation2 (G : Type*) [Magma G] (h : Equation15489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X3)) ◇ X3) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X3)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X2) ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ X2)) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2))) := superpose eq10 eq9
  have eq44 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X2) = X0 := superpose eq10 eq13
  have eq69 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((((X0 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) := superpose eq14 eq14
  have eq215 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq22
  have eq227 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0)))) = X3 := superpose eq22 eq9
  have eq276 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq10 eq215
  have eq310 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((((X0 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq276 eq69
  have eq313 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq276 eq310
  have eq316 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0))) = X3 := superpose eq313 eq227
  have eq461 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0)) = X3 := superpose eq313 eq316
  have eq462 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq313 eq461
  have eq483 (X0 X3 : G) : X0 = X3 := superpose eq44 eq462
  have eq537 (X0 : G) : sK0 ≠ X0 := superpose eq483 eq8
  subsumption eq537 eq483


@[equational_result]
theorem Equation15490_implies_Equation2 (G : Type*) [Magma G] (h : Equation15490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation15492_implies_Equation2 (G : Type*) [Magma G] (h : Equation15492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation15493_implies_Equation2 (G : Type*) [Magma G] (h : Equation15493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation15494_implies_Equation2 (G : Type*) [Magma G] (h : Equation15494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq11
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation15495_implies_Equation2 (G : Type*) [Magma G] (h : Equation15495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15497_implies_Equation2 (G : Type*) [Magma G] (h : Equation15497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq108 eq38


@[equational_result]
theorem Equation15498_implies_Equation2 (G : Type*) [Magma G] (h : Equation15498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq52 eq14


@[equational_result]
theorem Equation15499_implies_Equation2 (G : Type*) [Magma G] (h : Equation15499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation15501_implies_Equation2 (G : Type*) [Magma G] (h : Equation15501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation15503_implies_Equation2 (G : Type*) [Magma G] (h : Equation15503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation15505_implies_Equation2 (G : Type*) [Magma G] (h : Equation15505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq54 eq23


@[equational_result]
theorem Equation15506_implies_Equation2 (G : Type*) [Magma G] (h : Equation15506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq50 eq14


@[equational_result]
theorem Equation15507_implies_Equation2 (G : Type*) [Magma G] (h : Equation15507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15509_implies_Equation2 (G : Type*) [Magma G] (h : Equation15509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation15510_implies_Equation2 (G : Type*) [Magma G] (h : Equation15510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15511_implies_Equation2 (G : Type*) [Magma G] (h : Equation15511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X4 ◇ X0)) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation15512_implies_Equation2 (G : Type*) [Magma G] (h : Equation15512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15514_implies_Equation2 (G : Type*) [Magma G] (h : Equation15514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) ◇ (((X3 ◇ X0) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2))) := superpose eq7 eq10
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (((X2 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq10 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq10 eq12
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) = ((X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq7 eq15
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X2 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X2)) := superpose eq15 eq7
  have eq58 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq14 eq10
  have eq59 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = ((X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq14 eq15
  have eq61 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq10 eq25
  have eq63 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq14 eq25
  have eq75 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq25 eq10
  have eq81 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X2 := superpose eq75 eq40
  have eq83 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq81 eq63
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) = X1 := superpose eq81 eq29
  have eq88 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq81 eq59
  have eq93 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) ◇ X2) := superpose eq85 eq11
  have eq103 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq88 eq58
  have eq105 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = X1 := superpose eq81 eq103
  have eq106 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq105 eq83
  have eq107 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq105 eq61
  have eq114 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq107 eq106
  have eq120 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq75 eq114
  have eq124 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = X2 := superpose eq120 eq93
  have eq125 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq124 eq7
  have eq177 (X0 X2 : G) : X0 = X2 := superpose eq125 eq125
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq177 eq8
  subsumption eq179 eq177


@[equational_result]
theorem Equation15516_implies_Equation2 (G : Type*) [Magma G] (h : Equation15516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation15518_implies_Equation2 (G : Type*) [Magma G] (h : Equation15518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq34 eq13


@[equational_result]
theorem Equation15520_implies_Equation2 (G : Type*) [Magma G] (h : Equation15520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation15524_implies_Equation2 (G : Type*) [Magma G] (h : Equation15524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation15526_implies_Equation2 (G : Type*) [Magma G] (h : Equation15526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation15527_implies_Equation2 (G : Type*) [Magma G] (h : Equation15527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation15528_implies_Equation2 (G : Type*) [Magma G] (h : Equation15528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq65 eq17


@[equational_result]
theorem Equation15529_implies_Equation2 (G : Type*) [Magma G] (h : Equation15529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15532_implies_Equation2 (G : Type*) [Magma G] (h : Equation15532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (((X0 ◇ (X3 ◇ X3)) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation15533_implies_Equation2 (G : Type*) [Magma G] (h : Equation15533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15537_implies_Equation2 (G : Type*) [Magma G] (h : Equation15537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation15540_implies_Equation2 (G : Type*) [Magma G] (h : Equation15540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X3)) ◇ (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation15541_implies_Equation2 (G : Type*) [Magma G] (h : Equation15541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15543_implies_Equation2 (G : Type*) [Magma G] (h : Equation15543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation15544_implies_Equation2 (G : Type*) [Magma G] (h : Equation15544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ (((X0 ◇ (X3 ◇ X3)) ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation15545_implies_Equation2 (G : Type*) [Magma G] (h : Equation15545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X4 ◇ X4)) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation15546_implies_Equation2 (G : Type*) [Magma G] (h : Equation15546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15548_implies_Equation2 (G : Type*) [Magma G] (h : Equation15548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq37 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq13
  have eq72 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq37 eq7
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq9 eq72
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq112 eq85


@[equational_result]
theorem Equation15549_implies_Equation2 (G : Type*) [Magma G] (h : Equation15549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15550_implies_Equation2 (G : Type*) [Magma G] (h : Equation15550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (((X0 ◇ (X4 ◇ X5)) ◇ X0) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15551_implies_Equation2 (G : Type*) [Magma G] (h : Equation15551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15553_implies_Equation2 (G : Type*) [Magma G] (h : Equation15553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation15554_implies_Equation2 (G : Type*) [Magma G] (h : Equation15554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X2))) = X2 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation15555_implies_Equation2 (G : Type*) [Magma G] (h : Equation15555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation15556_implies_Equation2 (G : Type*) [Magma G] (h : Equation15556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation15558_implies_Equation2 (G : Type*) [Magma G] (h : Equation15558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X3)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq9 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq55 eq36


@[equational_result]
theorem Equation15559_implies_Equation2 (G : Type*) [Magma G] (h : Equation15559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X3 ◇ X4)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation15560_implies_Equation2 (G : Type*) [Magma G] (h : Equation15560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (((X0 ◇ (X4 ◇ X5)) ◇ X4) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15561_implies_Equation2 (G : Type*) [Magma G] (h : Equation15561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15563_implies_Equation2 (G : Type*) [Magma G] (h : Equation15563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation15564_implies_Equation2 (G : Type*) [Magma G] (h : Equation15564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15565_implies_Equation2 (G : Type*) [Magma G] (h : Equation15565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X0 ◇ (X4 ◇ X5)) ◇ X5) ◇ X5)) ◇ (((X0 ◇ (X4 ◇ X5)) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15566_implies_Equation2 (G : Type*) [Magma G] (h : Equation15566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15568_implies_Equation2 (G : Type*) [Magma G] (h : Equation15568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation15569_implies_Equation2 (G : Type*) [Magma G] (h : Equation15569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15570_implies_Equation2 (G : Type*) [Magma G] (h : Equation15570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X7) ◇ (((X0 ◇ (X4 ◇ X5)) ◇ X6) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15571_implies_Equation2 (G : Type*) [Magma G] (h : Equation15571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ (X5 ◇ X6)) ◇ X7) ◇ X7))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation15572_implies_Equation2 (G : Type*) [Magma G] (h : Equation15572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15575_implies_Equation2 (G : Type*) [Magma G] (h : Equation15575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq44 eq11


@[equational_result]
theorem Equation15578_implies_Equation2 (G : Type*) [Magma G] (h : Equation15578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq54 eq11


@[equational_result]
theorem Equation15580_implies_Equation2 (G : Type*) [Magma G] (h : Equation15580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation15582_implies_Equation2 (G : Type*) [Magma G] (h : Equation15582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation15585_implies_Equation2 (G : Type*) [Magma G] (h : Equation15585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation15588_implies_Equation2 (G : Type*) [Magma G] (h : Equation15588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation15590_implies_Equation2 (G : Type*) [Magma G] (h : Equation15590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation15592_implies_Equation2 (G : Type*) [Magma G] (h : Equation15592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15594_implies_Equation2 (G : Type*) [Magma G] (h : Equation15594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X1 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq11 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq11 eq17
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq18 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq9 eq19
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq33 eq23


@[equational_result]
theorem Equation15596_implies_Equation2 (G : Type*) [Magma G] (h : Equation15596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation15598_implies_Equation2 (G : Type*) [Magma G] (h : Equation15598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation15599_implies_Equation2 (G : Type*) [Magma G] (h : Equation15599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3))) = X2 := superpose eq10 eq9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq10 eq12
  have eq41 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) = (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (((X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq19 eq11
  have eq48 (X0 X1 X2 : G) : (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose eq10 eq11
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq11
  have eq51 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3))) := superpose eq11 eq12
  have eq61 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq50 eq10
  have eq68 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) = (X1 ◇ ((X1 ◇ X2) ◇ (((X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq50 eq41
  have eq73 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose eq50 eq48
  have eq75 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq61 eq19
  have eq80 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq61 eq12
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq61 eq75
  have eq122 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (X1 ◇ ((X1 ◇ X2) ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq61 eq68
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (X1 ◇ ((X1 ◇ X2) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq61 eq122
  have eq130 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose eq61 eq73
  have eq131 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq61 eq130
  have eq132 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X2 ◇ X0)) := superpose eq80 eq51
  have eq134 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq132 eq94
  have eq139 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X3))) := superpose eq132 eq123
  have eq140 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq132 eq131
  have eq170 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) := superpose eq132 eq139
  have eq171 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) := superpose eq132 eq170
  have eq172 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq132 eq171
  have eq173 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq132 eq140
  have eq174 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq173 eq172
  have eq177 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq174 eq134
  have eq185 (X0 X2 : G) : X0 = X2 := superpose eq177 eq177
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq185 eq8
  subsumption eq187 eq185


@[equational_result]
theorem Equation15600_implies_Equation2 (G : Type*) [Magma G] (h : Equation15600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation15602_implies_Equation2 (G : Type*) [Magma G] (h : Equation15602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X2)) = (X1 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq7 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = X1 := superpose eq10 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq10 eq21
  have eq41 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq43 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ (((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ X1) ◇ X3)) ◇ X3) = X0 := superpose eq10 eq9
  have eq52 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq41 eq27
  have eq63 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq41 eq52
  have eq64 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq41 eq63
  have eq74 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = (X1 ◇ X0) := superpose eq7 eq64
  have eq75 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X2) ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X0)) ◇ X1) := superpose eq9 eq64
  have eq89 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq74 eq11
  have eq99 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)) ◇ X3) = X0 := superpose eq74 eq43
  have eq108 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) := superpose eq74 eq75
  have eq130 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq64 eq41
  have eq133 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq10 eq41
  have eq144 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X0 ◇ X1) := superpose eq41 eq133
  have eq145 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq144 eq10
  have eq158 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq145 eq89
  have eq176 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq158 eq108
  have eq177 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq176 eq130
  have eq181 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X3) = X0 := superpose eq177 eq99
  have eq185 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq64 eq181
  have eq208 (X0 X2 : G) : X0 = X2 := superpose eq185 eq185
  have eq213 (X0 : G) : sK0 ≠ X0 := superpose eq208 eq8
  subsumption eq213 eq208


@[equational_result]
theorem Equation15603_implies_Equation2 (G : Type*) [Magma G] (h : Equation15603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) = X0 := superpose eq10 eq12
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X0) = X1 := superpose eq14 eq14
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ ((X2 ◇ X3) ◇ X3)) = ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X3) := superpose eq10 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) ◇ X2))) := superpose eq10 eq14
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) ◇ (X0 ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)))) = X2 := superpose eq10 eq14
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ X2))) := superpose eq10 eq21
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X2)))) := superpose eq10 eq26
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq16 eq10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := superpose eq35 eq14
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X3) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X3 ◇ X3))) := superpose eq35 eq20
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)))) = X2 := superpose eq35 eq22
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2)))) := superpose eq35 eq27
  have eq65 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := superpose eq35 eq45
  have eq66 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := superpose eq35 eq65
  have eq88 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq35 eq50
  have eq89 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ X3))))) := superpose eq35 eq88
  have eq90 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3)))))) := superpose eq35 eq89
  have eq91 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3)))))) = ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) ◇ X3) := superpose eq35 eq90
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3)))))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ X3) := superpose eq35 eq91
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) ◇ (X0 ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))))) = X2 := superpose eq35 eq51
  have eq94 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)))))) = X2 := superpose eq35 eq93
  have eq95 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X3 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))))))) = X2 := superpose eq35 eq94
  have eq96 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)))))))) = X2 := superpose eq35 eq95
  have eq97 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))))))))) = X2 := superpose eq35 eq96
  have eq98 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))))))))) = X2 := superpose eq35 eq97
  have eq99 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) = X2 := superpose eq66 eq98
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))))) := superpose eq35 eq53
  have eq103 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))))) := superpose eq35 eq102
  have eq104 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))))) := superpose eq35 eq103
  have eq207 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq66 eq66
  have eq215 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq207 eq104
  have eq223 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq207 eq215
  have eq225 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3)))))) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) := superpose eq223 eq92
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq223 eq99
  have eq238 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3)))))) := superpose eq223 eq225
  have eq239 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq223 eq238
  have eq242 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ X0) = X2 := superpose eq239 eq226
  have eq243 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq239 eq242
  have eq265 (X0 X1 : G) : X0 = X1 := superpose eq239 eq243
  have eq270 (X0 : G) : sK0 ≠ X0 := superpose eq265 eq8
  subsumption eq270 eq265


@[equational_result]
theorem Equation15604_implies_Equation2 (G : Type*) [Magma G] (h : Equation15604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation15606_implies_Equation2 (G : Type*) [Magma G] (h : Equation15606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation15607_implies_Equation2 (G : Type*) [Magma G] (h : Equation15607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq72 eq15


@[equational_result]
theorem Equation15608_implies_Equation2 (G : Type*) [Magma G] (h : Equation15608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation15609_implies_Equation2 (G : Type*) [Magma G] (h : Equation15609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15612_implies_Equation2 (G : Type*) [Magma G] (h : Equation15612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation15615_implies_Equation2 (G : Type*) [Magma G] (h : Equation15615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq61 eq11


@[equational_result]
theorem Equation15617_implies_Equation2 (G : Type*) [Magma G] (h : Equation15617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation15619_implies_Equation2 (G : Type*) [Magma G] (h : Equation15619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation15622_implies_Equation2 (G : Type*) [Magma G] (h : Equation15622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq66 eq11


@[equational_result]
theorem Equation15624_implies_Equation2 (G : Type*) [Magma G] (h : Equation15624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15625_implies_Equation2 (G : Type*) [Magma G] (h : Equation15625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15627_implies_Equation2 (G : Type*) [Magma G] (h : Equation15627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15628_implies_Equation2 (G : Type*) [Magma G] (h : Equation15628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15629_implies_Equation2 (G : Type*) [Magma G] (h : Equation15629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15631_implies_Equation2 (G : Type*) [Magma G] (h : Equation15631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq9
  have eq42 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq11
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq13 eq42
  have eq94 (X0 X3 : G) : X0 = X3 := superpose eq56 eq56
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq175 eq94


@[equational_result]
theorem Equation15632_implies_Equation2 (G : Type*) [Magma G] (h : Equation15632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X3) ◇ X4)) := superpose eq9 eq7
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X1 ◇ (X3 ◇ X2))) := superpose eq10 eq20
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq10 eq9
  have eq48 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X2))) = X3 := superpose eq23 eq34
  have eq50 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2)))) = X3 := superpose eq7 eq48
  have eq142 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq50
  have eq300 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq142
  have eq473 (X0 X2 : G) : X0 = X2 := superpose eq48 eq300
  have eq753 (X0 : G) : sK0 ≠ X0 := superpose eq473 eq8
  subsumption eq753 eq473


@[equational_result]
theorem Equation15633_implies_Equation2 (G : Type*) [Magma G] (h : Equation15633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation15635_implies_Equation2 (G : Type*) [Magma G] (h : Equation15635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15636_implies_Equation2 (G : Type*) [Magma G] (h : Equation15636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15637_implies_Equation2 (G : Type*) [Magma G] (h : Equation15637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15639_implies_Equation2 (G : Type*) [Magma G] (h : Equation15639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15640_implies_Equation2 (G : Type*) [Magma G] (h : Equation15640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15641_implies_Equation2 (G : Type*) [Magma G] (h : Equation15641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15643_implies_Equation2 (G : Type*) [Magma G] (h : Equation15643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15644_implies_Equation2 (G : Type*) [Magma G] (h : Equation15644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15645_implies_Equation2 (G : Type*) [Magma G] (h : Equation15645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15646_implies_Equation2 (G : Type*) [Magma G] (h : Equation15646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15648_implies_Equation2 (G : Type*) [Magma G] (h : Equation15648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2) = (X1 ◇ (((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq10 eq7
  have eq25 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0))) ◇ X0)) := superpose eq10 eq14
  have eq77 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq25 eq7
  have eq133 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) ◇ X1))) := superpose eq7 eq77
  have eq168 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) = (X0 ◇ X1) := superpose eq10 eq133
  have eq169 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq168 eq7
  have eq206 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq169 eq77
  have eq229 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq206 eq45
  have eq247 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq169 eq229
  have eq248 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq169 eq247
  have eq249 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq206 eq248
  have eq253 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq249 eq169
  have eq380 (X0 X2 : G) : X0 = X2 := superpose eq253 eq253
  have eq382 (X0 : G) : sK0 ≠ X0 := superpose eq380 eq8
  subsumption eq382 eq380


@[equational_result]
theorem Equation15650_implies_Equation2 (G : Type*) [Magma G] (h : Equation15650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15652_implies_Equation2 (G : Type*) [Magma G] (h : Equation15652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15654_implies_Equation2 (G : Type*) [Magma G] (h : Equation15654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation15658_implies_Equation2 (G : Type*) [Magma G] (h : Equation15658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation15660_implies_Equation2 (G : Type*) [Magma G] (h : Equation15660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation15661_implies_Equation2 (G : Type*) [Magma G] (h : Equation15661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation15662_implies_Equation2 (G : Type*) [Magma G] (h : Equation15662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq78 eq17


@[equational_result]
theorem Equation15663_implies_Equation2 (G : Type*) [Magma G] (h : Equation15663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15665_implies_Equation2 (G : Type*) [Magma G] (h : Equation15665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (((X4 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ X1)) := superpose eq10 eq11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq11 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X4 ◇ (X3 ◇ X1)) ◇ X5) := superpose eq13 eq13
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X4) = X0 := superpose eq7 eq13
  have eq47 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq13
  have eq87 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq46 eq24
  have eq97 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq47 eq45
  have eq99 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) = X2 := superpose eq97 eq87
  have eq100 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq97 eq99
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq100 eq31
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X0) = X1 := superpose eq100 eq101
  have eq114 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = X1 := superpose eq100 eq113
  have eq115 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq100 eq114
  have eq117 (X0 X1 : G) : X0 = X1 := superpose eq100 eq115
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq122 eq117


@[equational_result]
theorem Equation15667_implies_Equation2 (G : Type*) [Magma G] (h : Equation15667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15669_implies_Equation2 (G : Type*) [Magma G] (h : Equation15669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15670_implies_Equation2 (G : Type*) [Magma G] (h : Equation15670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15671_implies_Equation2 (G : Type*) [Magma G] (h : Equation15671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15673_implies_Equation2 (G : Type*) [Magma G] (h : Equation15673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15674_implies_Equation2 (G : Type*) [Magma G] (h : Equation15674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15675_implies_Equation2 (G : Type*) [Magma G] (h : Equation15675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15677_implies_Equation2 (G : Type*) [Magma G] (h : Equation15677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15678_implies_Equation2 (G : Type*) [Magma G] (h : Equation15678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15679_implies_Equation2 (G : Type*) [Magma G] (h : Equation15679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15680_implies_Equation2 (G : Type*) [Magma G] (h : Equation15680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15682_implies_Equation2 (G : Type*) [Magma G] (h : Equation15682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq14 eq14
  have eq32 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq18
  have eq85 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq32 eq32
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq7 eq85
  have eq342 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq342 eq173


@[equational_result]
theorem Equation15683_implies_Equation2 (G : Type*) [Magma G] (h : Equation15683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq9 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X0))))) = X3 := superpose eq14 eq14
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) := superpose eq14 eq9
  have eq48 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X1 := superpose eq18 eq18
  have eq60 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) = X0 := superpose eq48 eq28
  have eq64 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq60 eq7
  have eq83 (X0 X2 : G) : X0 = X2 := superpose eq14 eq64
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq107 eq83


@[equational_result]
theorem Equation15684_implies_Equation2 (G : Type*) [Magma G] (h : Equation15684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation15686_implies_Equation2 (G : Type*) [Magma G] (h : Equation15686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15687_implies_Equation2 (G : Type*) [Magma G] (h : Equation15687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15688_implies_Equation2 (G : Type*) [Magma G] (h : Equation15688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15690_implies_Equation2 (G : Type*) [Magma G] (h : Equation15690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15691_implies_Equation2 (G : Type*) [Magma G] (h : Equation15691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15692_implies_Equation2 (G : Type*) [Magma G] (h : Equation15692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15694_implies_Equation2 (G : Type*) [Magma G] (h : Equation15694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15695_implies_Equation2 (G : Type*) [Magma G] (h : Equation15695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15696_implies_Equation2 (G : Type*) [Magma G] (h : Equation15696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15697_implies_Equation2 (G : Type*) [Magma G] (h : Equation15697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15699_implies_Equation2 (G : Type*) [Magma G] (h : Equation15699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq37 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq13
  have eq76 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq37 eq7
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq9 eq76
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq112 eq85


@[equational_result]
theorem Equation15700_implies_Equation2 (G : Type*) [Magma G] (h : Equation15700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X5) ◇ X2)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq9
  have eq21 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = X4 := superpose eq12 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation15701_implies_Equation2 (G : Type*) [Magma G] (h : Equation15701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X5) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15702_implies_Equation2 (G : Type*) [Magma G] (h : Equation15702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15704_implies_Equation2 (G : Type*) [Magma G] (h : Equation15704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15705_implies_Equation2 (G : Type*) [Magma G] (h : Equation15705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15706_implies_Equation2 (G : Type*) [Magma G] (h : Equation15706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15707_implies_Equation2 (G : Type*) [Magma G] (h : Equation15707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15709_implies_Equation2 (G : Type*) [Magma G] (h : Equation15709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15710_implies_Equation2 (G : Type*) [Magma G] (h : Equation15710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15711_implies_Equation2 (G : Type*) [Magma G] (h : Equation15711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15712_implies_Equation2 (G : Type*) [Magma G] (h : Equation15712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15714_implies_Equation2 (G : Type*) [Magma G] (h : Equation15714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15715_implies_Equation2 (G : Type*) [Magma G] (h : Equation15715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15716_implies_Equation2 (G : Type*) [Magma G] (h : Equation15716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15717_implies_Equation2 (G : Type*) [Magma G] (h : Equation15717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15719_implies_Equation2 (G : Type*) [Magma G] (h : Equation15719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15720_implies_Equation2 (G : Type*) [Magma G] (h : Equation15720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15721_implies_Equation2 (G : Type*) [Magma G] (h : Equation15721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15722_implies_Equation2 (G : Type*) [Magma G] (h : Equation15722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15723_implies_Equation2 (G : Type*) [Magma G] (h : Equation15723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15725_implies_Equation2 (G : Type*) [Magma G] (h : Equation15725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X0) = ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X2) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X1) := superpose eq7 eq10
  have eq18 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose eq10 eq15
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq7
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0) = X3 := superpose eq18 eq10
  have eq24 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X0) = ((X2 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X2) := superpose eq18 eq13
  have eq26 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq18 eq21
  have eq28 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X0) = ((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X2) := superpose eq19 eq24
  have eq29 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = ((X3 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq26 eq28
  have eq30 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq29
  have eq31 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq30 eq18
  have eq32 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq31 eq30
  have eq37 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq32 eq19
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq37 eq37
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation15726_implies_Equation2 (G : Type*) [Magma G] (h : Equation15726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation15727_implies_Equation2 (G : Type*) [Magma G] (h : Equation15727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq69 eq14


@[equational_result]
theorem Equation15729_implies_Equation2 (G : Type*) [Magma G] (h : Equation15729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ (X3 ◇ X3))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq9
  have eq15 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq9
  have eq18 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq11 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq15
  have eq27 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq22 eq18
  have eq37 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq22 eq27
  have eq39 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq37 eq21
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq22
  have eq43 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq40 eq39
  have eq44 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq37 eq43
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq44 eq44
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq57 eq52


@[equational_result]
theorem Equation15731_implies_Equation2 (G : Type*) [Magma G] (h : Equation15731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq64 eq12


@[equational_result]
theorem Equation15734_implies_Equation2 (G : Type*) [Magma G] (h : Equation15734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq70 eq13


@[equational_result]
theorem Equation15735_implies_Equation2 (G : Type*) [Magma G] (h : Equation15735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15737_implies_Equation2 (G : Type*) [Magma G] (h : Equation15737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation15738_implies_Equation2 (G : Type*) [Magma G] (h : Equation15738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation15739_implies_Equation2 (G : Type*) [Magma G] (h : Equation15739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X4 ◇ (X0 ◇ X0)) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq73 eq13


@[equational_result]
theorem Equation15740_implies_Equation2 (G : Type*) [Magma G] (h : Equation15740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15742_implies_Equation2 (G : Type*) [Magma G] (h : Equation15742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ (((X3 ◇ X0) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X3 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X3 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) = ((((X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)))) ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)))) ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))))) := superpose eq9 eq9
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X2) ◇ X0)) = ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ ((((X3 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X0))) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0))) := superpose eq9 eq10
  have eq46 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = X1 := superpose eq15 eq7
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq15 eq7
  have eq102 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq46
  have eq139 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((((X3 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X3 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2))) := superpose eq15 eq11
  have eq184 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) := superpose eq15 eq102
  have eq185 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq102 eq102
  have eq186 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))) = X0 := superpose eq9 eq102
  have eq194 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)))) := superpose eq102 eq9
  have eq197 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = ((((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)))) := superpose eq102 eq11
  have eq203 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) = (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq102 eq15
  have eq205 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq102 eq11
  have eq208 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq102 eq10
  have eq239 (X0 X2 X3 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq102 eq194
  have eq240 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq185 eq239
  have eq242 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq102 eq197
  have eq243 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq185 eq242
  have eq244 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq240 eq243
  have eq248 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) := superpose eq244 eq203
  have eq249 (X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ X1)) := superpose eq248 eq184
  have eq254 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq249 eq102
  have eq259 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((((X2 ◇ X2) ◇ X2) ◇ X2) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X2))) := superpose eq254 eq139
  have eq264 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq254 eq205
  have eq265 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq254 eq264
  have eq269 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq254 eq208
  have eq270 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq254 eq269
  have eq271 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq270 eq265
  have eq273 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq270 eq271
  have eq274 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (((X2 ◇ X2) ◇ X2) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq273 eq259
  have eq281 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X2 ◇ X2) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2))) := superpose eq273 eq274
  have eq282 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X2 ◇ X2) := superpose eq273 eq281
  have eq284 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq282 eq15
  have eq332 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ X1) := superpose eq254 eq284
  have eq336 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq332 eq59
  have eq345 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq273 eq336
  have eq346 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq282 eq345
  have eq348 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))))) := superpose eq346 eq21
  have eq383 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) = (((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))))) := superpose eq254 eq348
  have eq384 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq273 eq383
  have eq385 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ (((X4 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) = (X0 ◇ X0) := superpose eq273 eq384
  have eq386 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq385 eq186
  have eq398 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq386 eq254
  have eq403 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq398 eq273
  have eq413 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ ((((X3 ◇ X2) ◇ X0) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0))) = X0 := superpose eq403 eq30
  have eq450 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ (((X3 ◇ X2) ◇ X0) ◇ X0)) = X0 := superpose eq403 eq413
  have eq451 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ X0)) = X0 := superpose eq403 eq450
  have eq452 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) = X0 := superpose eq403 eq451
  have eq453 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq403 eq452
  have eq454 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X0 := superpose eq403 eq453
  have eq455 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq403 eq454
  have eq456 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq403 eq455
  have eq457 (X0 X3 : G) : X0 = X3 := superpose eq456 eq456
  have eq462 (X0 : G) : sK0 ≠ X0 := superpose eq457 eq8
  subsumption eq462 eq457


@[equational_result]
theorem Equation15744_implies_Equation2 (G : Type*) [Magma G] (h : Equation15744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation15746_implies_Equation2 (G : Type*) [Magma G] (h : Equation15746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ (((X3 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq10 eq10
  have eq19 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) = (X0 ◇ (((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) ◇ X0)) := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq10 eq7
  have eq25 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose eq10 eq16
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq10 eq19
  have eq27 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = X1 := superpose eq26 eq25
  have eq28 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq27 eq20
  have eq29 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ (X2 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2))) = X2 := superpose eq28 eq9
  have eq30 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq28 eq15
  have eq32 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq29
  have eq33 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq28 eq30
  have eq37 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq28 eq24
  have eq38 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq37 eq33
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq38 eq26
  have eq40 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq38 eq12
  have eq46 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq40 eq32
  have eq54 (X0 X1 : G) : X0 = X1 := superpose eq46 eq39
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq68 eq54


@[equational_result]
theorem Equation15748_implies_Equation2 (G : Type*) [Magma G] (h : Equation15748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation15750_implies_Equation2 (G : Type*) [Magma G] (h : Equation15750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X1) = X0 := superpose eq10 eq18
  have eq103 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)))) ◇ X3) = X2 := superpose eq10 eq26
  have eq112 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = X1 := superpose eq10 eq26
  have eq140 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = X1 := superpose eq112 eq15
  have eq141 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X3) = X2 := superpose eq140 eq103
  have eq155 (X0 X3 : G) : X0 = X3 := superpose eq26 eq141
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq250 eq155


@[equational_result]
theorem Equation15751_implies_Equation2 (G : Type*) [Magma G] (h : Equation15751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X1) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0)) = X1 := superpose eq10 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := superpose eq10 eq7
  have eq92 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq18 eq19
  have eq105 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq92 eq7
  have eq106 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) = X2 := superpose eq92 eq9
  have eq156 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq92 eq105
  have eq157 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ ((X3 ◇ X0) ◇ X3)) = X2 := superpose eq92 eq106
  have eq158 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X3 ◇ X0)) = X2 := superpose eq92 eq157
  have eq159 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq92 eq158
  have eq160 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := superpose eq159 eq21
  have eq163 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq156 eq160
  have eq164 (X0 X3 : G) : X0 = X3 := superpose eq163 eq163
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq175 eq164


@[equational_result]
theorem Equation15752_implies_Equation2 (G : Type*) [Magma G] (h : Equation15752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq60 eq12


@[equational_result]
theorem Equation15754_implies_Equation2 (G : Type*) [Magma G] (h : Equation15754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation15755_implies_Equation2 (G : Type*) [Magma G] (h : Equation15755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq72 eq15


@[equational_result]
theorem Equation15756_implies_Equation2 (G : Type*) [Magma G] (h : Equation15756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ (((X4 ◇ X0) ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq70 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = ((X4 ◇ X3) ◇ X1) := superpose eq9 eq7
  have eq81 (X0 X1 X4 X5 : G) : ((X4 ◇ X5) ◇ X1) = X0 := superpose eq7 eq70
  have eq210 (X0 X6 : G) : X0 = X6 := superpose eq9 eq81
  have eq381 (X0 : G) : sK0 ≠ X0 := superpose eq210 eq8
  subsumption eq381 eq210


@[equational_result]
theorem Equation15757_implies_Equation2 (G : Type*) [Magma G] (h : Equation15757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15760_implies_Equation2 (G : Type*) [Magma G] (h : Equation15760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15761_implies_Equation2 (G : Type*) [Magma G] (h : Equation15761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq66 eq13


@[equational_result]
theorem Equation15763_implies_Equation2 (G : Type*) [Magma G] (h : Equation15763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq19 (X0 X2 X4 : G) : (X4 ◇ ((X2 ◇ X4) ◇ X4)) = X0 := superpose eq7 eq10
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq159 eq74


@[equational_result]
theorem Equation15765_implies_Equation2 (G : Type*) [Magma G] (h : Equation15765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation15767_implies_Equation2 (G : Type*) [Magma G] (h : Equation15767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X3) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq46 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0)) ◇ X0) ◇ X2) = X3 := superpose eq10 eq11
  have eq51 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = X3 := superpose eq7 eq46
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq134 eq59


@[equational_result]
theorem Equation15768_implies_Equation2 (G : Type*) [Magma G] (h : Equation15768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ X0) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2)) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15769_implies_Equation2 (G : Type*) [Magma G] (h : Equation15769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15771_implies_Equation2 (G : Type*) [Magma G] (h : Equation15771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation15772_implies_Equation2 (G : Type*) [Magma G] (h : Equation15772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X0) ◇ X5) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15773_implies_Equation2 (G : Type*) [Magma G] (h : Equation15773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X4 ◇ (X0 ◇ X4)) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq69 eq14


@[equational_result]
theorem Equation15774_implies_Equation2 (G : Type*) [Magma G] (h : Equation15774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15776_implies_Equation2 (G : Type*) [Magma G] (h : Equation15776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ X0) = (X1 ◇ ((X0 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq9
  have eq21 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ X0) = (X1 ◇ ((X0 ◇ X4) ◇ X1)) := superpose eq12 eq10
  have eq22 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ X0) = X4 := superpose eq12 eq21
  have eq24 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq22 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq9 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation15777_implies_Equation2 (G : Type*) [Magma G] (h : Equation15777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15778_implies_Equation2 (G : Type*) [Magma G] (h : Equation15778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X0) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15779_implies_Equation2 (G : Type*) [Magma G] (h : Equation15779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15781_implies_Equation2 (G : Type*) [Magma G] (h : Equation15781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq74 eq19


@[equational_result]
theorem Equation15782_implies_Equation2 (G : Type*) [Magma G] (h : Equation15782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation15783_implies_Equation2 (G : Type*) [Magma G] (h : Equation15783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X3) ◇ X5))) = X3 := superpose eq7 eq7
  have eq61 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = (X1 ◇ X0) := superpose eq7 eq9
  have eq74 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq61 eq7
  have eq121 (X0 X3 : G) : X0 = X3 := superpose eq74 eq74
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq123 eq121


@[equational_result]
theorem Equation15784_implies_Equation2 (G : Type*) [Magma G] (h : Equation15784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation15786_implies_Equation2 (G : Type*) [Magma G] (h : Equation15786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation15787_implies_Equation2 (G : Type*) [Magma G] (h : Equation15787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation15788_implies_Equation2 (G : Type*) [Magma G] (h : Equation15788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X4) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15789_implies_Equation2 (G : Type*) [Magma G] (h : Equation15789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15791_implies_Equation2 (G : Type*) [Magma G] (h : Equation15791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X5) ◇ X3)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ X4) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (X4 ◇ ((((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X5) ◇ X4)) := superpose eq7 eq10
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = X1 := superpose eq10 eq7
  have eq52 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X1) ◇ X4)) = X0 := superpose eq7 eq52
  have eq120 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq68 eq15
  have eq124 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X1 := superpose eq120 eq27
  have eq172 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq120 eq124
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq172 eq172
  have eq192 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq192 eq173


@[equational_result]
theorem Equation15792_implies_Equation2 (G : Type*) [Magma G] (h : Equation15792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15793_implies_Equation2 (G : Type*) [Magma G] (h : Equation15793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X5) ◇ X5)) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15794_implies_Equation2 (G : Type*) [Magma G] (h : Equation15794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation15796_implies_Equation2 (G : Type*) [Magma G] (h : Equation15796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation15797_implies_Equation2 (G : Type*) [Magma G] (h : Equation15797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15798_implies_Equation2 (G : Type*) [Magma G] (h : Equation15798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X7) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ X6) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15799_implies_Equation2 (G : Type*) [Magma G] (h : Equation15799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ (((X5 ◇ (X0 ◇ X6)) ◇ X7) ◇ X7))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation15800_implies_Equation2 (G : Type*) [Magma G] (h : Equation15800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15802_implies_Equation2 (G : Type*) [Magma G] (h : Equation15802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = (X1 ◇ (((X2 ◇ X0) ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq7 eq9
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose eq28 eq7
  have eq45 (X0 X1 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ X0)) = X1 := superpose eq28 eq7
  have eq79 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) = ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)))) := superpose eq9 eq42
  have eq80 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = (X0 ◇ (X0 ◇ (((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0))) := superpose eq10 eq42
  have eq84 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq42
  have eq85 (X0 X1 X2 X3 : G) : ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1))) = X1 := superpose eq9 eq42
  have eq91 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq42 eq7
  have eq139 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) = (X1 ◇ ((((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1))) ◇ (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1)) ◇ X1)) := superpose eq9 eq45
  have eq234 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X0) = (X0 ◇ (((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X0)) ◇ X0)) := superpose eq7 eq91
  have eq235 (X0 X1 X2 X3 : G) : ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ (((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1))) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1))) := superpose eq9 eq91
  have eq267 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X0) := superpose eq84 eq234
  have eq272 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq267 eq84
  have eq275 (X0 X1 X2 X3 : G) : ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1))) := superpose eq85 eq235
  have eq276 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X2) = ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) := superpose eq7 eq275
  have eq277 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) := superpose eq267 eq276
  have eq279 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) = (X1 ◇ ((((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1)) ◇ X1)) := superpose eq277 eq139
  have eq281 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) = ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq277 eq79
  have eq283 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) = (X1 ◇ ((X1 ◇ (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1)) ◇ X1)) := superpose eq272 eq279
  have eq284 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) = (X1 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X1)) := superpose eq9 eq283
  have eq285 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X1) = (((X3 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) := superpose eq272 eq281
  have eq286 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = (X1 ◇ ((((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) := superpose eq285 eq9
  have eq302 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X1) = (X1 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X1)) := superpose eq285 eq284
  have eq303 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) = ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X1) := superpose eq286 eq302
  have eq331 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = (X1 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq303 eq286
  have eq355 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X0 := superpose eq7 eq331
  have eq357 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq355 eq7
  have eq410 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = (X0 ◇ (((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0)) := superpose eq357 eq80
  have eq521 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = (X0 ◇ X0) := superpose eq357 eq410
  have eq522 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq357 eq521
  have eq523 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq357 eq522
  have eq524 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq357 eq523
  have eq800 (X0 X1 : G) : X0 = X1 := superpose eq357 eq524
  have eq810 (X0 : G) : sK0 ≠ X0 := superpose eq800 eq8
  subsumption eq810 eq800


@[equational_result]
theorem Equation15804_implies_Equation2 (G : Type*) [Magma G] (h : Equation15804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation15806_implies_Equation2 (G : Type*) [Magma G] (h : Equation15806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2) ◇ X2) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) = X1 := superpose eq9 eq7
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) = X2 := superpose eq25 eq24
  have eq38 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X0 ◇ X2)) ◇ X0) = (((X3 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ ((X3 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0))) ◇ ((X3 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0)))) := superpose eq9 eq10
  have eq58 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq25 eq25
  have eq67 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) = X2 := superpose eq25 eq10
  have eq77 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq67 eq29
  have eq82 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq77 eq34
  have eq83 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X0 ◇ X2)) ◇ X0) = (((X3 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0))) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0)))) := superpose eq77 eq38
  have eq116 (X0 X2 X4 : G) : ((X4 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq77 eq83
  have eq117 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq82 eq116
  have eq118 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq117 eq58
  have eq131 (X0 X1 : G) : X0 = X1 := superpose eq117 eq118
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq136 eq131


@[equational_result]
theorem Equation15808_implies_Equation2 (G : Type*) [Magma G] (h : Equation15808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation15810_implies_Equation2 (G : Type*) [Magma G] (h : Equation15810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1) = (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X4 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2)) ◇ X4) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X5 ◇ (((X4 ◇ X2) ◇ X4) ◇ X1)) ◇ X5) ◇ X1)) = (((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) ◇ X3) ◇ X1) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = (X0 ◇ (((X4 ◇ X2) ◇ X4) ◇ X0)) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : (((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) ◇ X2) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) = X2 := superpose eq24 eq21
  have eq48 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X2 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3))) = (((X2 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) := superpose eq10 eq9
  have eq56 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X2) ◇ X4) ◇ X1) = (((X3 ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1))) ◇ X3) ◇ X1) := superpose eq9 eq24
  have eq75 (X1 X2 X3 X4 : G) : (((X4 ◇ X2) ◇ X4) ◇ X1) = (((X3 ◇ X2) ◇ X3) ◇ X1) := superpose eq7 eq56
  have eq91 (X0 X1 X2 X3 : G) : (X1 ◇ (((X3 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) ◇ X3) ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose eq33 eq9
  have eq101 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) ◇ X3) ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq91 eq12
  have eq102 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq101 eq11
  have eq105 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X3) := superpose eq102 eq102
  have eq130 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq102 eq33
  have eq150 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X2) = (X2 ◇ (((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4) ◇ X2)) := superpose eq102 eq9
  have eq167 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X3)) = (X3 ◇ (((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4) ◇ X3)) := superpose eq102 eq17
  have eq479 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X2) = X3 := superpose eq75 eq24
  have eq483 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ X3))) = X2 := superpose eq75 eq33
  have eq1293 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := superpose eq483 eq130
  have eq1536 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ X1) ◇ X2) ◇ X1) := superpose eq1293 eq102
  have eq1540 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq1293 eq33
  have eq2944 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X3) = (X1 ◇ (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X1)) := superpose eq1536 eq7
  have eq3159 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq1540 eq24
  have eq3349 (X0 X1 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq3159 eq479
  have eq3622 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0)) ◇ X1))) = X0 := superpose eq3349 eq33
  have eq3640 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq3622
  have eq3644 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq3640 eq130
  have eq3764 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X3) := superpose eq3644 eq105
  have eq4325 (X1 X2 X3 X4 : G) : (X3 ◇ (((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4) ◇ X3)) = (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) := superpose eq3764 eq167
  have eq4411 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X2) = (X3 ◇ (((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4) ◇ X3)) := superpose eq3644 eq4325
  have eq4412 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X2) := superpose eq4411 eq150
  have eq4417 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq4412 eq2944
  have eq4418 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq4412 eq91
  have eq4422 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq3644 eq4418
  have eq4424 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ X1)) := superpose eq4422 eq4417
  have eq4550 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = X1 := superpose eq3644 eq4424
  have eq4573 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq4550 eq7
  have eq4579 (X0 X1 X2 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq4550 eq48
  have eq4808 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq4550 eq4573
  have eq4846 (X0 X1 X2 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq4808 eq4579
  have eq4847 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq4808 eq4846
  have eq4848 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq4808 eq4847
  have eq4849 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq4808 eq4848
  have eq4850 (X0 X3 : G) : X0 = X3 := superpose eq4849 eq4849
  have eq4855 (X0 : G) : sK0 ≠ X0 := superpose eq4850 eq8
  subsumption eq4855 eq4850


@[equational_result]
theorem Equation15812_implies_Equation2 (G : Type*) [Magma G] (h : Equation15812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq64 eq12


@[equational_result]
theorem Equation15814_implies_Equation2 (G : Type*) [Magma G] (h : Equation15814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation15815_implies_Equation2 (G : Type*) [Magma G] (h : Equation15815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation15816_implies_Equation2 (G : Type*) [Magma G] (h : Equation15816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X0 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X4 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0))) = X3 := superpose eq21 eq11
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq26
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq53 eq42


@[equational_result]
theorem Equation15817_implies_Equation2 (G : Type*) [Magma G] (h : Equation15817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15819_implies_Equation2 (G : Type*) [Magma G] (h : Equation15819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 : G) : (X2 ◇ ((X4 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq7
  have eq15 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1)) := superpose eq9 eq7
  have eq16 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X0))) = X3 := superpose eq9 eq7
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) = X3 := superpose eq9 eq14
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq9
  have eq48 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X0))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))))) := superpose eq9 eq15
  have eq49 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2)))) = ((X2 ◇ X2) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq14 eq15
  have eq57 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) ◇ X0))) := superpose eq9 eq15
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq7 eq15
  have eq82 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))))) := superpose eq14 eq48
  have eq83 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := superpose eq16 eq49
  have eq89 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) = (X3 ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq14 eq57
  have eq90 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X3 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq59 eq89
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))))) := superpose eq59 eq82
  have eq95 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq83 eq90
  have eq96 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))))) := superpose eq59 eq91
  have eq97 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq83 eq96
  have eq98 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X1 := superpose eq97 eq95
  have eq101 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X3) = X3 := superpose eq97 eq19
  have eq113 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq101 eq83
  have eq119 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq113 eq25
  have eq121 (X0 X1 X2 X4 : G) : (X2 ◇ ((X4 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq119 eq11
  have eq128 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X2 := superpose eq119 eq121
  have eq132 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq128 eq98
  have eq137 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq132 eq7
  have eq151 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq132 eq137
  have eq157 (X0 X2 : G) : X0 = X2 := superpose eq151 eq151
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq159 eq157


@[equational_result]
theorem Equation15821_implies_Equation2 (G : Type*) [Magma G] (h : Equation15821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation15823_implies_Equation2 (G : Type*) [Magma G] (h : Equation15823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15824_implies_Equation2 (G : Type*) [Magma G] (h : Equation15824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15825_implies_Equation2 (G : Type*) [Magma G] (h : Equation15825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15827_implies_Equation2 (G : Type*) [Magma G] (h : Equation15827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15828_implies_Equation2 (G : Type*) [Magma G] (h : Equation15828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation15829_implies_Equation2 (G : Type*) [Magma G] (h : Equation15829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15831_implies_Equation2 (G : Type*) [Magma G] (h : Equation15831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15832_implies_Equation2 (G : Type*) [Magma G] (h : Equation15832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15833_implies_Equation2 (G : Type*) [Magma G] (h : Equation15833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15834_implies_Equation2 (G : Type*) [Magma G] (h : Equation15834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15836_implies_Equation2 (G : Type*) [Magma G] (h : Equation15836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X0) ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((((((X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X4) ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq9 eq7
  have eq26 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ (X4 ◇ X1)) ◇ X4) ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq11 eq22
  have eq34 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq10
  have eq54 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq34 eq34
  have eq95 (X0 X1 X2 X4 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X4) ◇ (X2 ◇ (X0 ◇ X2)))) = X4 := superpose eq11 eq9
  have eq99 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) ◇ X0)) ◇ X1)) := superpose eq11 eq7
  have eq118 (X0 X2 X4 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X4 ◇ X0))) = X4 := superpose eq26 eq95
  have eq131 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X4 ◇ (X3 ◇ X0)))) = X4 := superpose eq10 eq118
  have eq136 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X1)) ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X0)) := superpose eq34 eq118
  have eq142 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) := superpose eq34 eq118
  have eq144 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) := superpose eq118 eq10
  have eq160 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := superpose eq118 eq34
  have eq164 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X1)) := superpose eq142 eq99
  have eq175 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq142 eq164
  have eq176 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq54 eq144
  have eq184 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) := superpose eq176 eq136
  have eq213 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) = X0 := superpose eq34 eq175
  have eq223 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((((X3 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq7 eq175
  have eq280 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) := superpose eq213 eq184
  have eq283 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq142 eq223
  have eq284 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq283 eq176
  have eq297 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X2 ◇ (X3 ◇ X2))) := superpose eq284 eq280
  have eq320 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq297 eq160
  have eq326 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq320 eq131
  have eq329 (X2 X3 : G) : (X3 ◇ X2) = X3 := superpose eq326 eq297
  have eq333 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq329 eq7
  have eq381 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq329 eq333
  have eq382 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq329 eq381
  have eq383 (X0 X3 : G) : X0 = X3 := superpose eq382 eq382
  have eq385 (X0 : G) : sK0 ≠ X0 := superpose eq383 eq8
  subsumption eq385 eq383


@[equational_result]
theorem Equation15838_implies_Equation2 (G : Type*) [Magma G] (h : Equation15838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation15840_implies_Equation2 (G : Type*) [Magma G] (h : Equation15840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15841_implies_Equation2 (G : Type*) [Magma G] (h : Equation15841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15842_implies_Equation2 (G : Type*) [Magma G] (h : Equation15842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15844_implies_Equation2 (G : Type*) [Magma G] (h : Equation15844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15845_implies_Equation2 (G : Type*) [Magma G] (h : Equation15845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15846_implies_Equation2 (G : Type*) [Magma G] (h : Equation15846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15848_implies_Equation2 (G : Type*) [Magma G] (h : Equation15848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15849_implies_Equation2 (G : Type*) [Magma G] (h : Equation15849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15850_implies_Equation2 (G : Type*) [Magma G] (h : Equation15850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15851_implies_Equation2 (G : Type*) [Magma G] (h : Equation15851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15853_implies_Equation2 (G : Type*) [Magma G] (h : Equation15853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X7 ◇ X0) ◇ ((X4 ◇ (X5 ◇ X6)) ◇ X7)) = (((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X5 ◇ X6)) ◇ X7)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X5 ◇ X6)) ◇ X7)))) := superpose eq10 eq10
  have eq34 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X0) = X1 := superpose eq10 eq9
  have eq42 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq12 eq12
  have eq99 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X0) = ((X5 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X6) := superpose eq10 eq42
  have eq169 (X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X6) = X1 := superpose eq34 eq99
  have eq171 (X0 X4 X5 X6 X7 : G) : ((X7 ◇ X0) ◇ ((X4 ◇ (X5 ◇ X6)) ◇ X7)) = X7 := superpose eq169 eq23
  have eq172 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq171 eq34
  have eq174 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq172 eq16
  have eq200 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = X4 := superpose eq172 eq174
  have eq201 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq172 eq200
  have eq202 (X0 X3 : G) : X0 = X3 := superpose eq201 eq201
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq202 eq8
  subsumption eq207 eq202


@[equational_result]
theorem Equation15854_implies_Equation2 (G : Type*) [Magma G] (h : Equation15854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq9 eq9
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq147 eq61


@[equational_result]
theorem Equation15855_implies_Equation2 (G : Type*) [Magma G] (h : Equation15855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ (((X3 ◇ (X1 ◇ X4)) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X4 X5 : G) : (((X1 ◇ X5) ◇ X0) ◇ X4) = (X1 ◇ (X0 ◇ X5)) := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X4))))) = X5 := superpose eq22 eq9
  have eq32 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X5 ◇ X0))) = X5 := superpose eq22 eq28
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq10 eq32
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq46 eq39


@[equational_result]
theorem Equation15856_implies_Equation2 (G : Type*) [Magma G] (h : Equation15856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15858_implies_Equation2 (G : Type*) [Magma G] (h : Equation15858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15859_implies_Equation2 (G : Type*) [Magma G] (h : Equation15859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15860_implies_Equation2 (G : Type*) [Magma G] (h : Equation15860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15861_implies_Equation2 (G : Type*) [Magma G] (h : Equation15861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15863_implies_Equation2 (G : Type*) [Magma G] (h : Equation15863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15864_implies_Equation2 (G : Type*) [Magma G] (h : Equation15864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15865_implies_Equation2 (G : Type*) [Magma G] (h : Equation15865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15866_implies_Equation2 (G : Type*) [Magma G] (h : Equation15866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15868_implies_Equation2 (G : Type*) [Magma G] (h : Equation15868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15869_implies_Equation2 (G : Type*) [Magma G] (h : Equation15869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15870_implies_Equation2 (G : Type*) [Magma G] (h : Equation15870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15871_implies_Equation2 (G : Type*) [Magma G] (h : Equation15871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15873_implies_Equation2 (G : Type*) [Magma G] (h : Equation15873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15874_implies_Equation2 (G : Type*) [Magma G] (h : Equation15874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15875_implies_Equation2 (G : Type*) [Magma G] (h : Equation15875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15876_implies_Equation2 (G : Type*) [Magma G] (h : Equation15876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15877_implies_Equation2 (G : Type*) [Magma G] (h : Equation15877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15880_implies_Equation2 (G : Type*) [Magma G] (h : Equation15880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq52 eq14


@[equational_result]
theorem Equation15881_implies_Equation2 (G : Type*) [Magma G] (h : Equation15881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation15885_implies_Equation2 (G : Type*) [Magma G] (h : Equation15885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation15888_implies_Equation2 (G : Type*) [Magma G] (h : Equation15888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq74 eq14


@[equational_result]
theorem Equation15889_implies_Equation2 (G : Type*) [Magma G] (h : Equation15889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15891_implies_Equation2 (G : Type*) [Magma G] (h : Equation15891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation15892_implies_Equation2 (G : Type*) [Magma G] (h : Equation15892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15893_implies_Equation2 (G : Type*) [Magma G] (h : Equation15893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X4 ◇ (X4 ◇ X0)) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation15894_implies_Equation2 (G : Type*) [Magma G] (h : Equation15894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15896_implies_Equation2 (G : Type*) [Magma G] (h : Equation15896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) ◇ (((X2 ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X0)) = (((((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4) ◇ (X3 ◇ (X3 ◇ X0))) := superpose eq10 eq10
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X4)) = ((X0 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0)) ◇ (X3 ◇ (X3 ◇ X4))) := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X3 ◇ ((X0 ◇ (((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X3) ◇ X0)) ◇ X3)) := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : ((((((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4) ◇ (X3 ◇ (X3 ◇ X0))) ◇ ((((X3 ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) ◇ (((((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4) ◇ (X3 ◇ (X3 ◇ X0))))) = X5 := superpose eq10 eq9
  have eq33 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq9 eq10
  have eq37 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X0)) ◇ ((((X3 ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) ◇ (X0 ◇ (X4 ◇ X0)))) = X5 := superpose eq11 eq28
  have eq43 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3))) ◇ ((((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq16
  have eq46 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq16 eq16
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = ((X3 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq7 eq16
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq16 eq10
  have eq58 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X2 ◇ (X2 ◇ X3))) ◇ ((X0 ◇ X4) ◇ (((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X2 ◇ (X2 ◇ X3))))) = X4 := superpose eq16 eq9
  have eq64 (X0 X3 X4 : G) : ((X3 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) ◇ ((X0 ◇ X4) ◇ (X3 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)))) = X4 := superpose eq10 eq58
  have eq87 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq16 eq37
  have eq104 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq87 eq33
  have eq325 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose eq87 eq7
  have eq351 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq87 eq17
  have eq352 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) = ((((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq87 eq10
  have eq392 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ ((X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq10 eq351
  have eq393 (X1 X2 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) = ((X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq10 eq352
  have eq414 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((((((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq87 eq11
  have eq439 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ (((X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)) := superpose eq9 eq11
  have eq496 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((((X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq10 eq414
  have eq503 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) := superpose eq10 eq439
  have eq504 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq56 eq503
  have eq506 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ ((X0 ◇ X4) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3))))) = X4 := superpose eq504 eq64
  have eq507 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq504 eq392
  have eq508 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq16 eq507
  have eq537 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq325 eq325
  have eq544 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose eq47 eq325
  have eq550 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq325 eq87
  have eq587 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (((X2 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq544 eq496
  have eq588 (X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X2))) = X2 := superpose eq544 eq393
  have eq589 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq588 eq537
  have eq592 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq588 eq508
  have eq594 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq589 eq56
  have eq595 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq589 eq104
  have eq603 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq589 eq504
  have eq605 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X4) ◇ (X0 ◇ (X3 ◇ X3)))) = X4 := superpose eq589 eq506
  have eq609 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq592 eq594
  have eq622 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq16 eq550
  have eq623 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq588 eq622
  have eq624 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq623 eq587
  have eq626 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq623 eq595
  have eq631 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq623 eq603
  have eq633 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X4) ◇ (X0 ◇ X3))) = X4 := superpose eq623 eq605
  have eq634 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq623 eq609
  have eq639 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq592 eq626
  have eq640 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq624 eq639
  have eq641 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq623 eq640
  have eq642 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq623 eq641
  have eq643 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq623 eq642
  have eq676 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq643 eq631
  have eq677 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq634 eq7
  have eq687 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) = X3 := superpose eq634 eq43
  have eq770 (X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = X2 := superpose eq687 eq46
  have eq773 (X0 X1 X3 X4 : G) : (X4 ◇ (X0 ◇ X4)) = ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0)) ◇ (X3 ◇ (X3 ◇ X4))) := superpose eq770 eq12
  have eq926 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X4)) = ((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X4) ◇ X0)) ◇ X4) := superpose eq770 eq773
  have eq927 (X0 X4 : G) : (X4 ◇ (X0 ◇ X4)) = ((X0 ◇ ((X0 ◇ X4) ◇ X0)) ◇ X4) := superpose eq770 eq926
  have eq928 (X0 X4 : G) : (X4 ◇ (X0 ◇ X4)) = ((X0 ◇ (X0 ◇ (X4 ◇ X0))) ◇ X4) := superpose eq643 eq927
  have eq929 (X0 X4 : G) : (X4 ◇ (X0 ◇ X4)) = (X4 ◇ X4) := superpose eq677 eq928
  have eq930 (X0 X4 : G) : (X4 ◇ (X0 ◇ X4)) = X4 := superpose eq623 eq929
  have eq931 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq930 eq676
  have eq945 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq623 eq931
  have eq946 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq945 eq633
  have eq949 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X3)) = X4 := superpose eq945 eq946
  have eq950 (X3 X4 : G) : (X3 ◇ X3) = X4 := superpose eq945 eq949
  have eq1005 (X0 X1 : G) : X0 = X1 := superpose eq945 eq950
  have eq1019 (X0 : G) : sK0 ≠ X0 := superpose eq1005 eq8
  subsumption eq1019 eq1005


@[equational_result]
theorem Equation15897_implies_Equation2 (G : Type*) [Magma G] (h : Equation15897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (((X3 ◇ (X3 ◇ X2)) ◇ X0) ◇ X3)) ◇ X1) ◇ ((X0 ◇ X4) ◇ X2)) = X4 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2))) ◇ (((X3 ◇ X4) ◇ X0) ◇ X3)) ◇ X1) ◇ ((X0 ◇ X5) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2))) = X5 := superpose eq9 eq9
  have eq26 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((((X2 ◇ (X2 ◇ X0)) ◇ X1) ◇ X4) ◇ (X2 ◇ (X2 ◇ X0)))) = X4 := superpose eq10 eq9
  have eq27 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ (X3 ◇ X4)) ◇ (X4 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq9
  have eq46 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0) = X2 := superpose eq27 eq27
  have eq181 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose eq28 eq26
  have eq247 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq181 eq181
  have eq263 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq181 eq27
  have eq266 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) ◇ ((X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ X0))) ◇ X1) = X0 := superpose eq181 eq46
  have eq270 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq181 eq247
  have eq271 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq181 eq270
  have eq280 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) ◇ X0)) ◇ X1) = X0 := superpose eq181 eq266
  have eq289 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq181 eq14
  have eq344 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq181 eq289
  have eq345 (X0 X1 X3 X4 : G) : ((X3 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq344
  have eq346 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ X1) = X0 := superpose eq345 eq280
  have eq347 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq346 eq271
  have eq373 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X0 := superpose eq347 eq27
  have eq408 (X0 X2 : G) : (X2 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = X0 := superpose eq373 eq263
  have eq420 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq408 eq346
  have eq429 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ (((X3 ◇ X4) ◇ X0) ◇ X3)) ◇ X1) ◇ ((X0 ◇ X5) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2))) = X5 := superpose eq420 eq15
  have eq601 (X0 X1 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ (((X3 ◇ X4) ◇ X0) ◇ X3)) ◇ X1) ◇ (X0 ◇ X5)) = X5 := superpose eq420 eq429
  have eq602 (X0 X1 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ (((X3 ◇ X4) ◇ X0) ◇ X3)) ◇ X1) ◇ X0) = X5 := superpose eq420 eq601
  have eq603 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (((X3 ◇ X4) ◇ X0) ◇ X3)) ◇ X0) = X5 := superpose eq420 eq602
  have eq604 (X0 X1 X5 : G) : ((X1 ◇ X1) ◇ X0) = X5 := superpose eq420 eq603
  have eq605 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq347 eq604
  have eq606 (X0 X1 : G) : X0 = X1 := superpose eq347 eq605
  have eq611 (X0 : G) : sK0 ≠ X0 := superpose eq606 eq8
  subsumption eq611 eq606


@[equational_result]
theorem Equation15898_implies_Equation2 (G : Type*) [Magma G] (h : Equation15898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation15900_implies_Equation2 (G : Type*) [Magma G] (h : Equation15900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15901_implies_Equation2 (G : Type*) [Magma G] (h : Equation15901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15902_implies_Equation2 (G : Type*) [Magma G] (h : Equation15902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15904_implies_Equation2 (G : Type*) [Magma G] (h : Equation15904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15905_implies_Equation2 (G : Type*) [Magma G] (h : Equation15905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15906_implies_Equation2 (G : Type*) [Magma G] (h : Equation15906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15908_implies_Equation2 (G : Type*) [Magma G] (h : Equation15908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15909_implies_Equation2 (G : Type*) [Magma G] (h : Equation15909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15910_implies_Equation2 (G : Type*) [Magma G] (h : Equation15910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15911_implies_Equation2 (G : Type*) [Magma G] (h : Equation15911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15913_implies_Equation2 (G : Type*) [Magma G] (h : Equation15913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq9
  have eq67 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq9 eq13
  have eq114 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq67 eq7
  have eq144 (X0 X3 : G) : X0 = X3 := superpose eq9 eq114
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq163 eq144


@[equational_result]
theorem Equation15914_implies_Equation2 (G : Type*) [Magma G] (h : Equation15914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation15915_implies_Equation2 (G : Type*) [Magma G] (h : Equation15915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15917_implies_Equation2 (G : Type*) [Magma G] (h : Equation15917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15918_implies_Equation2 (G : Type*) [Magma G] (h : Equation15918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation15919_implies_Equation2 (G : Type*) [Magma G] (h : Equation15919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15921_implies_Equation2 (G : Type*) [Magma G] (h : Equation15921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15922_implies_Equation2 (G : Type*) [Magma G] (h : Equation15922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15923_implies_Equation2 (G : Type*) [Magma G] (h : Equation15923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15925_implies_Equation2 (G : Type*) [Magma G] (h : Equation15925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15926_implies_Equation2 (G : Type*) [Magma G] (h : Equation15926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15927_implies_Equation2 (G : Type*) [Magma G] (h : Equation15927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15928_implies_Equation2 (G : Type*) [Magma G] (h : Equation15928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15930_implies_Equation2 (G : Type*) [Magma G] (h : Equation15930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq43 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq14
  have eq80 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq43 eq7
  have eq94 (X0 X4 : G) : X0 = X4 := superpose eq9 eq80
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq122 eq94


@[equational_result]
theorem Equation15931_implies_Equation2 (G : Type*) [Magma G] (h : Equation15931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation15932_implies_Equation2 (G : Type*) [Magma G] (h : Equation15932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ (((X3 ◇ (X3 ◇ X4)) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation15933_implies_Equation2 (G : Type*) [Magma G] (h : Equation15933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15935_implies_Equation2 (G : Type*) [Magma G] (h : Equation15935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15936_implies_Equation2 (G : Type*) [Magma G] (h : Equation15936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15937_implies_Equation2 (G : Type*) [Magma G] (h : Equation15937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15938_implies_Equation2 (G : Type*) [Magma G] (h : Equation15938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15940_implies_Equation2 (G : Type*) [Magma G] (h : Equation15940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15941_implies_Equation2 (G : Type*) [Magma G] (h : Equation15941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15942_implies_Equation2 (G : Type*) [Magma G] (h : Equation15942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15943_implies_Equation2 (G : Type*) [Magma G] (h : Equation15943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15945_implies_Equation2 (G : Type*) [Magma G] (h : Equation15945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15946_implies_Equation2 (G : Type*) [Magma G] (h : Equation15946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15947_implies_Equation2 (G : Type*) [Magma G] (h : Equation15947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15948_implies_Equation2 (G : Type*) [Magma G] (h : Equation15948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15950_implies_Equation2 (G : Type*) [Magma G] (h : Equation15950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15951_implies_Equation2 (G : Type*) [Magma G] (h : Equation15951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15952_implies_Equation2 (G : Type*) [Magma G] (h : Equation15952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15953_implies_Equation2 (G : Type*) [Magma G] (h : Equation15953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15954_implies_Equation2 (G : Type*) [Magma G] (h : Equation15954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation15956_implies_Equation2 (G : Type*) [Magma G] (h : Equation15956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X5)) ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq32 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X0) ◇ X3) = X0 := superpose eq11 eq11
  have eq35 (X0 X5 X6 : G) : ((X5 ◇ (X6 ◇ X0)) ◇ X0) = (X0 ◇ ((X5 ◇ (X6 ◇ X0)) ◇ X0)) := superpose eq11 eq11
  have eq36 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq42 (X0 X5 X6 : G) : (X6 ◇ X0) = ((X5 ◇ (X6 ◇ X0)) ◇ X0) := superpose eq10 eq35
  have eq49 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X3) = X0 := superpose eq42 eq32
  have eq51 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq36 eq13
  have eq52 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq51 eq49
  have eq53 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq51 eq10
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq53 eq52
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq70 eq65


@[equational_result]
theorem Equation15957_implies_Equation2 (G : Type*) [Magma G] (h : Equation15957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation15958_implies_Equation2 (G : Type*) [Magma G] (h : Equation15958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq53 eq14


@[equational_result]
theorem Equation15959_implies_Equation2 (G : Type*) [Magma G] (h : Equation15959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation15961_implies_Equation2 (G : Type*) [Magma G] (h : Equation15961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation15962_implies_Equation2 (G : Type*) [Magma G] (h : Equation15962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq76 eq18


@[equational_result]
theorem Equation15963_implies_Equation2 (G : Type*) [Magma G] (h : Equation15963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X2))) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X3)) = X0 := superpose eq20 eq7
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq20 eq25
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq20 eq36
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation15964_implies_Equation2 (G : Type*) [Magma G] (h : Equation15964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation15966_implies_Equation2 (G : Type*) [Magma G] (h : Equation15966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation15967_implies_Equation2 (G : Type*) [Magma G] (h : Equation15967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation15968_implies_Equation2 (G : Type*) [Magma G] (h : Equation15968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15969_implies_Equation2 (G : Type*) [Magma G] (h : Equation15969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15971_implies_Equation2 (G : Type*) [Magma G] (h : Equation15971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X4)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq90 eq24


@[equational_result]
theorem Equation15972_implies_Equation2 (G : Type*) [Magma G] (h : Equation15972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15973_implies_Equation2 (G : Type*) [Magma G] (h : Equation15973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X3 ◇ (X4 ◇ X0)) ◇ X4) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation15974_implies_Equation2 (G : Type*) [Magma G] (h : Equation15974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15976_implies_Equation2 (G : Type*) [Magma G] (h : Equation15976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation15977_implies_Equation2 (G : Type*) [Magma G] (h : Equation15977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15978_implies_Equation2 (G : Type*) [Magma G] (h : Equation15978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15979_implies_Equation2 (G : Type*) [Magma G] (h : Equation15979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ (((X5 ◇ (X6 ◇ X0)) ◇ X7) ◇ X7))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation15980_implies_Equation2 (G : Type*) [Magma G] (h : Equation15980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation15982_implies_Equation2 (G : Type*) [Magma G] (h : Equation15982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X5 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq27 (X0 X1 X2 X3 X4 X7 X8 : G) : (X4 ◇ ((X7 ◇ (X8 ◇ X0)) ◇ X4)) = ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq11 eq7
  have eq41 (X0 X2 X3 X4 X7 X8 : G) : (X4 ◇ ((X7 ◇ (X8 ◇ X0)) ◇ X4)) = ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq10 eq27
  have eq49 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq13
  have eq93 (X0 X2 X3 X4 : G) : (X4 ◇ X0) = ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq49 eq41
  have eq101 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq49 eq93
  have eq102 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq101 eq34
  have eq113 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq101 eq102
  have eq114 (X0 X3 : G) : X0 = X3 := superpose eq113 eq113
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq119 eq114


@[equational_result]
theorem Equation15983_implies_Equation2 (G : Type*) [Magma G] (h : Equation15983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X2)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq132 eq45


@[equational_result]
theorem Equation15984_implies_Equation2 (G : Type*) [Magma G] (h : Equation15984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) ◇ (((X4 ◇ X0) ◇ X5) ◇ X3)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X0))) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq10
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq9 eq20
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq146 eq60


@[equational_result]
theorem Equation15985_implies_Equation2 (G : Type*) [Magma G] (h : Equation15985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation15987_implies_Equation2 (G : Type*) [Magma G] (h : Equation15987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15988_implies_Equation2 (G : Type*) [Magma G] (h : Equation15988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15989_implies_Equation2 (G : Type*) [Magma G] (h : Equation15989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15990_implies_Equation2 (G : Type*) [Magma G] (h : Equation15990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15992_implies_Equation2 (G : Type*) [Magma G] (h : Equation15992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15993_implies_Equation2 (G : Type*) [Magma G] (h : Equation15993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15994_implies_Equation2 (G : Type*) [Magma G] (h : Equation15994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15995_implies_Equation2 (G : Type*) [Magma G] (h : Equation15995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation15997_implies_Equation2 (G : Type*) [Magma G] (h : Equation15997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15998_implies_Equation2 (G : Type*) [Magma G] (h : Equation15998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation15999_implies_Equation2 (G : Type*) [Magma G] (h : Equation15999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16000_implies_Equation2 (G : Type*) [Magma G] (h : Equation16000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16002_implies_Equation2 (G : Type*) [Magma G] (h : Equation16002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16003_implies_Equation2 (G : Type*) [Magma G] (h : Equation16003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16004_implies_Equation2 (G : Type*) [Magma G] (h : Equation16004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16005_implies_Equation2 (G : Type*) [Magma G] (h : Equation16005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16006_implies_Equation2 (G : Type*) [Magma G] (h : Equation16006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16008_implies_Equation2 (G : Type*) [Magma G] (h : Equation16008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq52 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq14
  have eq96 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq52 eq7
  have eq112 (X0 X3 : G) : X0 = X3 := superpose eq10 eq96
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq131 eq112


@[equational_result]
theorem Equation16009_implies_Equation2 (G : Type*) [Magma G] (h : Equation16009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((((((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X2) ◇ X0) ◇ X5) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16010_implies_Equation2 (G : Type*) [Magma G] (h : Equation16010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation16011_implies_Equation2 (G : Type*) [Magma G] (h : Equation16011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16013_implies_Equation2 (G : Type*) [Magma G] (h : Equation16013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16014_implies_Equation2 (G : Type*) [Magma G] (h : Equation16014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16015_implies_Equation2 (G : Type*) [Magma G] (h : Equation16015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16016_implies_Equation2 (G : Type*) [Magma G] (h : Equation16016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16018_implies_Equation2 (G : Type*) [Magma G] (h : Equation16018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16019_implies_Equation2 (G : Type*) [Magma G] (h : Equation16019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16020_implies_Equation2 (G : Type*) [Magma G] (h : Equation16020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16021_implies_Equation2 (G : Type*) [Magma G] (h : Equation16021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16023_implies_Equation2 (G : Type*) [Magma G] (h : Equation16023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16024_implies_Equation2 (G : Type*) [Magma G] (h : Equation16024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16025_implies_Equation2 (G : Type*) [Magma G] (h : Equation16025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16026_implies_Equation2 (G : Type*) [Magma G] (h : Equation16026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16028_implies_Equation2 (G : Type*) [Magma G] (h : Equation16028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16029_implies_Equation2 (G : Type*) [Magma G] (h : Equation16029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16030_implies_Equation2 (G : Type*) [Magma G] (h : Equation16030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16031_implies_Equation2 (G : Type*) [Magma G] (h : Equation16031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16032_implies_Equation2 (G : Type*) [Magma G] (h : Equation16032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16034_implies_Equation2 (G : Type*) [Magma G] (h : Equation16034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq9
  have eq70 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq9 eq13
  have eq117 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq70 eq7
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq9 eq117
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq162 eq143


@[equational_result]
theorem Equation16035_implies_Equation2 (G : Type*) [Magma G] (h : Equation16035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation16036_implies_Equation2 (G : Type*) [Magma G] (h : Equation16036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X5) ◇ (((X3 ◇ (X4 ◇ X4)) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation16037_implies_Equation2 (G : Type*) [Magma G] (h : Equation16037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16039_implies_Equation2 (G : Type*) [Magma G] (h : Equation16039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16040_implies_Equation2 (G : Type*) [Magma G] (h : Equation16040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16041_implies_Equation2 (G : Type*) [Magma G] (h : Equation16041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16042_implies_Equation2 (G : Type*) [Magma G] (h : Equation16042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16044_implies_Equation2 (G : Type*) [Magma G] (h : Equation16044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16045_implies_Equation2 (G : Type*) [Magma G] (h : Equation16045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16046_implies_Equation2 (G : Type*) [Magma G] (h : Equation16046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16047_implies_Equation2 (G : Type*) [Magma G] (h : Equation16047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16049_implies_Equation2 (G : Type*) [Magma G] (h : Equation16049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16050_implies_Equation2 (G : Type*) [Magma G] (h : Equation16050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16051_implies_Equation2 (G : Type*) [Magma G] (h : Equation16051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16052_implies_Equation2 (G : Type*) [Magma G] (h : Equation16052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16054_implies_Equation2 (G : Type*) [Magma G] (h : Equation16054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16055_implies_Equation2 (G : Type*) [Magma G] (h : Equation16055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16056_implies_Equation2 (G : Type*) [Magma G] (h : Equation16056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16057_implies_Equation2 (G : Type*) [Magma G] (h : Equation16057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16058_implies_Equation2 (G : Type*) [Magma G] (h : Equation16058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16060_implies_Equation2 (G : Type*) [Magma G] (h : Equation16060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X7 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X7) ◇ X1)) = X7 := superpose eq7 eq7
  have eq10 (X0 X1 X6 : G) : (X1 ◇ ((X0 ◇ X6) ◇ X1)) = X6 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq43 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq14
  have eq80 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X1)) = X0 := superpose eq43 eq7
  have eq94 (X0 X4 : G) : X0 = X4 := superpose eq9 eq80
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq122 eq94


