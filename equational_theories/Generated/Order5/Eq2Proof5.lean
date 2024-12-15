import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation12380_implies_Equation2 (G : Type*) [Magma G] (h : Equation12380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq135 eq46


@[equational_result]
theorem Equation12381_implies_Equation2 (G : Type*) [Magma G] (h : Equation12381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12383_implies_Equation2 (G : Type*) [Magma G] (h : Equation12383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq67 eq17


@[equational_result]
theorem Equation12384_implies_Equation2 (G : Type*) [Magma G] (h : Equation12384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation12385_implies_Equation2 (G : Type*) [Magma G] (h : Equation12385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation12386_implies_Equation2 (G : Type*) [Magma G] (h : Equation12386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12388_implies_Equation2 (G : Type*) [Magma G] (h : Equation12388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X3 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2)))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ X3) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = ((((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) ◇ X0) ◇ (((X4 ◇ X4) ◇ (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) ◇ X3)) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq15 eq10
  have eq32 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = X2 := superpose eq15 eq7
  have eq36 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq15 eq7
  have eq55 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq15 eq32
  have eq72 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq55 eq29
  have eq133 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq72 eq7
  have eq137 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq72 eq13
  have eq144 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ X2)) := superpose eq72 eq10
  have eq178 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq55 eq137
  have eq275 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq133 eq10
  have eq327 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X3 ◇ X3) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq275 eq36
  have eq328 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X2)))) = X3 := superpose eq327 eq9
  have eq330 (X0 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq327 eq15
  have eq353 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq328 eq144
  have eq358 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq330 eq178
  have eq381 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq330 eq353
  have eq451 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X3 ◇ X3) ◇ X2)) := superpose eq330 eq381
  have eq531 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq328
  have eq537 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X2)) = ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq13 eq328
  have eq548 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X2)) = X2 := superpose eq7 eq537
  have eq549 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X2)) = X2 := superpose eq330 eq548
  have eq550 (X2 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X3 ◇ X3) ◇ X2)) = X2 := superpose eq451 eq549
  have eq551 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq550 eq358
  have eq553 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq551 eq531
  have eq558 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = X3 := superpose eq553 eq328
  have eq571 (X0 X3 : G) : X0 = X3 := superpose eq10 eq558
  have eq628 (X0 : G) : sK0 ≠ X0 := superpose eq571 eq8
  subsumption eq628 eq571


@[equational_result]
theorem Equation12390_implies_Equation2 (G : Type*) [Magma G] (h : Equation12390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq70 eq19


@[equational_result]
theorem Equation12392_implies_Equation2 (G : Type*) [Magma G] (h : Equation12392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12393_implies_Equation2 (G : Type*) [Magma G] (h : Equation12393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12394_implies_Equation2 (G : Type*) [Magma G] (h : Equation12394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12396_implies_Equation2 (G : Type*) [Magma G] (h : Equation12396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12397_implies_Equation2 (G : Type*) [Magma G] (h : Equation12397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12398_implies_Equation2 (G : Type*) [Magma G] (h : Equation12398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12400_implies_Equation2 (G : Type*) [Magma G] (h : Equation12400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12401_implies_Equation2 (G : Type*) [Magma G] (h : Equation12401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12402_implies_Equation2 (G : Type*) [Magma G] (h : Equation12402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12403_implies_Equation2 (G : Type*) [Magma G] (h : Equation12403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12405_implies_Equation2 (G : Type*) [Magma G] (h : Equation12405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ X3) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ X3) ◇ (X0 ◇ X2)) = ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X4 ◇ X4) ◇ X4) ◇ X2)) := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X4 ◇ X4) ◇ X4) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3)))) = X2 := superpose eq10 eq9
  have eq40 (X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ (((X4 ◇ X4) ◇ X4) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3)))) = X2 := superpose eq23 eq31
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq17 eq7
  have eq71 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq23 eq59
  have eq201 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq71 eq71
  have eq349 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((((X2 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((((X2 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0))) = X0 := superpose eq9 eq201
  have eq406 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X0))) = X0 := superpose eq23 eq349
  have eq5513 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X3 ◇ X3) ◇ X3) ◇ X1)) ◇ (X4 ◇ X2))) = X4 := superpose eq29 eq7
  have eq5525 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) = (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) ◇ ((X3 ◇ X3) ◇ X3)) := superpose eq29 eq23
  have eq5797 (X1 X2 X4 : G) : (X2 ◇ (X1 ◇ (X4 ◇ X2))) = X4 := superpose eq9 eq5513
  have eq5803 (X1 X3 : G) : (X1 ◇ ((X3 ◇ X3) ◇ X3)) = X1 := superpose eq9 eq5525
  have eq5813 (X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ (((X4 ◇ X4) ◇ X4) ◇ X2)) = X2 := superpose eq5803 eq40
  have eq6079 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq5813 eq406
  have eq6097 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq6079 eq23
  have eq6154 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq6079 eq6097
  have eq6155 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq6079 eq6154
  have eq6156 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq6079 eq6155
  have eq6157 (X1 X2 X4 : G) : (X2 ◇ (X1 ◇ X4)) = X4 := superpose eq6156 eq5797
  have eq6159 (X1 X2 X4 : G) : (X2 ◇ X1) = X4 := superpose eq6156 eq6157
  have eq6168 (X0 X3 : G) : X0 = X3 := superpose eq6159 eq6159
  have eq6179 (X0 : G) : sK0 ≠ X0 := superpose eq6168 eq8
  subsumption eq6179 eq6168


@[equational_result]
theorem Equation12406_implies_Equation2 (G : Type*) [Magma G] (h : Equation12406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq13
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq58 eq21


@[equational_result]
theorem Equation12407_implies_Equation2 (G : Type*) [Magma G] (h : Equation12407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ X3) = (X1 ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq129 eq47


@[equational_result]
theorem Equation12409_implies_Equation2 (G : Type*) [Magma G] (h : Equation12409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12410_implies_Equation2 (G : Type*) [Magma G] (h : Equation12410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12411_implies_Equation2 (G : Type*) [Magma G] (h : Equation12411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12413_implies_Equation2 (G : Type*) [Magma G] (h : Equation12413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12414_implies_Equation2 (G : Type*) [Magma G] (h : Equation12414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12415_implies_Equation2 (G : Type*) [Magma G] (h : Equation12415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12417_implies_Equation2 (G : Type*) [Magma G] (h : Equation12417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12418_implies_Equation2 (G : Type*) [Magma G] (h : Equation12418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12419_implies_Equation2 (G : Type*) [Magma G] (h : Equation12419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12420_implies_Equation2 (G : Type*) [Magma G] (h : Equation12420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12422_implies_Equation2 (G : Type*) [Magma G] (h : Equation12422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ X4) = ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq44 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq11 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X4 ◇ X4) ◇ X5)) = (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq11 eq9
  have eq51 (X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X2 ◇ ((X4 ◇ X4) ◇ X5)) := superpose eq44 eq45
  have eq52 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq44 eq51
  have eq53 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X0 := superpose eq52 eq7
  have eq64 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq52 eq53
  have eq65 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq52 eq64
  have eq66 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq68 eq66


@[equational_result]
theorem Equation12423_implies_Equation2 (G : Type*) [Magma G] (h : Equation12423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation12424_implies_Equation2 (G : Type*) [Magma G] (h : Equation12424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (((X3 ◇ X3) ◇ X4) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X0)) = X5 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation12425_implies_Equation2 (G : Type*) [Magma G] (h : Equation12425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (X1 ◇ (X0 ◇ (X6 ◇ X7))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation12427_implies_Equation2 (G : Type*) [Magma G] (h : Equation12427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12428_implies_Equation2 (G : Type*) [Magma G] (h : Equation12428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12429_implies_Equation2 (G : Type*) [Magma G] (h : Equation12429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12430_implies_Equation2 (G : Type*) [Magma G] (h : Equation12430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12432_implies_Equation2 (G : Type*) [Magma G] (h : Equation12432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12433_implies_Equation2 (G : Type*) [Magma G] (h : Equation12433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12434_implies_Equation2 (G : Type*) [Magma G] (h : Equation12434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12435_implies_Equation2 (G : Type*) [Magma G] (h : Equation12435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12437_implies_Equation2 (G : Type*) [Magma G] (h : Equation12437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12438_implies_Equation2 (G : Type*) [Magma G] (h : Equation12438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12439_implies_Equation2 (G : Type*) [Magma G] (h : Equation12439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12440_implies_Equation2 (G : Type*) [Magma G] (h : Equation12440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12442_implies_Equation2 (G : Type*) [Magma G] (h : Equation12442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12443_implies_Equation2 (G : Type*) [Magma G] (h : Equation12443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12444_implies_Equation2 (G : Type*) [Magma G] (h : Equation12444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12445_implies_Equation2 (G : Type*) [Magma G] (h : Equation12445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12446_implies_Equation2 (G : Type*) [Magma G] (h : Equation12446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12448_implies_Equation2 (G : Type*) [Magma G] (h : Equation12448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) ◇ (((X4 ◇ X5) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq9 eq9
  have eq42 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X6)))) ◇ (((X3 ◇ X0) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X6))) ◇ X6)) ◇ X0) = X6 := superpose eq9 eq11
  have eq55 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = ((X3 ◇ X0) ◇ X3) := superpose eq11 eq18
  have eq117 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X4))) ◇ X4) := superpose eq9 eq55
  have eq124 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq18 eq55
  have eq176 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X6)))) ◇ ((X4 ◇ X5) ◇ X6)) ◇ X0) = X6 := superpose eq124 eq42
  have eq179 (X0 X4 X5 X6 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X6)) ◇ X0) = X6 := superpose eq117 eq176
  have eq269 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq179 eq179
  have eq401 (X0 X4 : G) : X0 = X4 := superpose eq11 eq269
  have eq539 (X0 : G) : sK0 ≠ X0 := superpose eq401 eq8
  subsumption eq539 eq401


@[equational_result]
theorem Equation12449_implies_Equation2 (G : Type*) [Magma G] (h : Equation12449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X4) ◇ X0) = (X1 ◇ X0) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (((X2 ◇ X4) ◇ X5) ◇ ((X0 ◇ X1) ◇ X2))) = X5 := superpose eq12 eq7
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq9
  have eq54 (X1 X3 X5 : G) : (X3 ◇ X1) = X5 := superpose eq36 eq27
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq54
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq149 eq55


@[equational_result]
theorem Equation12450_implies_Equation2 (G : Type*) [Magma G] (h : Equation12450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X5 ◇ (((X3 ◇ X4) ◇ X0) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X0)) = X5 := superpose eq7 eq9
  have eq39 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq13
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq120 eq52


@[equational_result]
theorem Equation12451_implies_Equation2 (G : Type*) [Magma G] (h : Equation12451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq105 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq127 (X0 X5 : G) : X0 = X5 := superpose eq7 eq105
  have eq265 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq265 eq127


@[equational_result]
theorem Equation12453_implies_Equation2 (G : Type*) [Magma G] (h : Equation12453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X1 ◇ X1))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11
  have eq37 (X0 X3 : G) : (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X3 := superpose eq22 eq7
  have eq51 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq14 eq37
  have eq80 (X0 X2 : G) : X0 = X2 := superpose eq51 eq51
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq111 eq80


@[equational_result]
theorem Equation12454_implies_Equation2 (G : Type*) [Magma G] (h : Equation12454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq9 eq9
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq171 eq77


@[equational_result]
theorem Equation12455_implies_Equation2 (G : Type*) [Magma G] (h : Equation12455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X1 ◇ (((X3 ◇ X4) ◇ X0) ◇ (X2 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ ((X2 ◇ X3) ◇ X5)) = (X1 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq32 (X0 X1 X2 X4 X5 X6 X7 X8 : G) : (X8 ◇ (((X5 ◇ X2) ◇ X4) ◇ (X8 ◇ X7))) = ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X6 ◇ X7) ◇ X1)) := superpose eq10 eq10
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X8 : G) : (X8 ◇ (X6 ◇ (X8 ◇ X1))) = (((X3 ◇ ((X4 ◇ X2) ◇ X5)) ◇ X6) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X9 ◇ (X8 ◇ (X9 ◇ X7))) = (((X5 ◇ (X2 ◇ ((X6 ◇ X7) ◇ X4))) ◇ X8) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X1))) := superpose eq10 eq10
  have eq82 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X1 := superpose eq10 eq20
  have eq111 (X1 X6 X8 : G) : (X8 ◇ (X6 ◇ (X8 ◇ X1))) = X1 := superpose eq82 eq40
  have eq112 (X0 X1 X2 X6 X7 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X6 ◇ X7) ◇ X1)) = X7 := superpose eq111 eq32
  have eq124 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (((X5 ◇ (X2 ◇ ((X6 ◇ X7) ◇ X4))) ◇ X8) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X1))) = X7 := superpose eq111 eq41
  have eq134 (X1 X2 X6 X7 : G) : (X2 ◇ ((X6 ◇ X7) ◇ X1)) = X7 := superpose eq111 eq112
  have eq168 (X2 X4 X5 X6 X7 X8 : G) : (((X5 ◇ (X2 ◇ ((X6 ◇ X7) ◇ X4))) ◇ X8) ◇ X4) = X7 := superpose eq134 eq124
  have eq169 (X4 X5 X7 X8 : G) : (((X5 ◇ X7) ◇ X8) ◇ X4) = X7 := superpose eq134 eq168
  have eq170 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq169 eq7
  have eq171 (X0 X3 : G) : X0 = X3 := superpose eq20 eq170
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq171 eq8
  subsumption eq180 eq171


@[equational_result]
theorem Equation12456_implies_Equation2 (G : Type*) [Magma G] (h : Equation12456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation12458_implies_Equation2 (G : Type*) [Magma G] (h : Equation12458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X2 ◇ X1))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq40 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq12 eq9
  have eq44 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq40 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq137 eq47


@[equational_result]
theorem Equation12459_implies_Equation2 (G : Type*) [Magma G] (h : Equation12459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X2 ◇ X2))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq157 eq60


@[equational_result]
theorem Equation12460_implies_Equation2 (G : Type*) [Magma G] (h : Equation12460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation12461_implies_Equation2 (G : Type*) [Magma G] (h : Equation12461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12463_implies_Equation2 (G : Type*) [Magma G] (h : Equation12463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X3 ◇ X4) ◇ X0) ◇ (X4 ◇ X2)) ◇ X1))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X0)) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X6 X7 : G) : ((X1 ◇ (X0 ◇ X7)) ◇ X6) = X7 := superpose eq12 eq12
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X5)) ◇ X0) ◇ X1))) = X5 := superpose eq12 eq7
  have eq28 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X2)) = X5 := superpose eq18 eq9
  have eq33 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq28 eq22
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq128 eq42


@[equational_result]
theorem Equation12464_implies_Equation2 (G : Type*) [Magma G] (h : Equation12464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq73 eq13


@[equational_result]
theorem Equation12465_implies_Equation2 (G : Type*) [Magma G] (h : Equation12465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X3 ◇ X4) ◇ X0) ◇ (X4 ◇ X4)) ◇ (((X3 ◇ X4) ◇ X0) ◇ (X4 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X0)) = X5 := superpose eq7 eq9
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq12
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq153 eq56


@[equational_result]
theorem Equation12466_implies_Equation2 (G : Type*) [Magma G] (h : Equation12466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12468_implies_Equation2 (G : Type*) [Magma G] (h : Equation12468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq43 eq32


@[equational_result]
theorem Equation12469_implies_Equation2 (G : Type*) [Magma G] (h : Equation12469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12470_implies_Equation2 (G : Type*) [Magma G] (h : Equation12470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation12471_implies_Equation2 (G : Type*) [Magma G] (h : Equation12471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (X2 ◇ (X0 ◇ X1)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation12472_implies_Equation2 (G : Type*) [Magma G] (h : Equation12472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12474_implies_Equation2 (G : Type*) [Magma G] (h : Equation12474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X2 := superpose eq9 eq9
  have eq47 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq13
  have eq105 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq47 eq7
  have eq155 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) ◇ X4) = (((X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) ◇ X4)) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0)))) := superpose eq15 eq47
  have eq162 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq47 eq105
  have eq164 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq105
  have eq194 (X0 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) ◇ X4) = (((X0 ◇ X0) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0)))) := superpose eq164 eq155
  have eq207 (X0 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) ◇ X4) = ((X0 ◇ X0) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0)))) := superpose eq162 eq194
  have eq208 (X0 X2 X3 X4 : G) : (X0 ◇ X0) = ((X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) ◇ X4) := superpose eq162 eq207
  have eq209 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) = X2 := superpose eq208 eq15
  have eq284 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) = (((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4))) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)))) := superpose eq7 eq209
  have eq301 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) = ((X4 ◇ X4) ◇ ((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)))) := superpose eq208 eq284
  have eq302 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) = (X4 ◇ X4) := superpose eq162 eq301
  have eq303 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq302 eq7
  have eq431 (X0 X2 : G) : X0 = X2 := superpose eq303 eq303
  have eq433 (X0 : G) : sK0 ≠ X0 := superpose eq431 eq8
  subsumption eq433 eq431


@[equational_result]
theorem Equation12475_implies_Equation2 (G : Type*) [Magma G] (h : Equation12475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X2)) ◇ X5) ◇ X1) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq36 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X0 := superpose eq9 eq12
  have eq47 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ X5) ◇ X1) ◇ X0)) = X4 := superpose eq36 eq11
  have eq57 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X5)) = X4 := superpose eq36 eq47
  have eq58 (X1 X2 X4 : G) : (X1 ◇ X2) = X4 := superpose eq36 eq57
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq70 eq59


@[equational_result]
theorem Equation12476_implies_Equation2 (G : Type*) [Magma G] (h : Equation12476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ (X0 ◇ X4))) ◇ X1) ◇ X0)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X0 := superpose eq7 eq12
  have eq27 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq21 eq7
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X1) ◇ X0)) = X5 := superpose eq21 eq11
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X5 := superpose eq21 eq29
  have eq41 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq27 eq40
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq27 eq41
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq53 eq44


@[equational_result]
theorem Equation12477_implies_Equation2 (G : Type*) [Magma G] (h : Equation12477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation12479_implies_Equation2 (G : Type*) [Magma G] (h : Equation12479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12480_implies_Equation2 (G : Type*) [Magma G] (h : Equation12480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12481_implies_Equation2 (G : Type*) [Magma G] (h : Equation12481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12482_implies_Equation2 (G : Type*) [Magma G] (h : Equation12482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12484_implies_Equation2 (G : Type*) [Magma G] (h : Equation12484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12485_implies_Equation2 (G : Type*) [Magma G] (h : Equation12485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12486_implies_Equation2 (G : Type*) [Magma G] (h : Equation12486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12487_implies_Equation2 (G : Type*) [Magma G] (h : Equation12487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12489_implies_Equation2 (G : Type*) [Magma G] (h : Equation12489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12490_implies_Equation2 (G : Type*) [Magma G] (h : Equation12490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12491_implies_Equation2 (G : Type*) [Magma G] (h : Equation12491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12492_implies_Equation2 (G : Type*) [Magma G] (h : Equation12492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12494_implies_Equation2 (G : Type*) [Magma G] (h : Equation12494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12495_implies_Equation2 (G : Type*) [Magma G] (h : Equation12495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12496_implies_Equation2 (G : Type*) [Magma G] (h : Equation12496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12497_implies_Equation2 (G : Type*) [Magma G] (h : Equation12497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12498_implies_Equation2 (G : Type*) [Magma G] (h : Equation12498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12500_implies_Equation2 (G : Type*) [Magma G] (h : Equation12500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ (((X4 ◇ X5) ◇ X4) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq9
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq12 eq12
  have eq133 (X0 X3 : G) : X0 = X3 := superpose eq10 eq60
  have eq267 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq267 eq133


@[equational_result]
theorem Equation12501_implies_Equation2 (G : Type*) [Magma G] (h : Equation12501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X0)) = X5 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation12502_implies_Equation2 (G : Type*) [Magma G] (h : Equation12502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation12503_implies_Equation2 (G : Type*) [Magma G] (h : Equation12503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (X1 ◇ (X0 ◇ (X6 ◇ X7))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation12505_implies_Equation2 (G : Type*) [Magma G] (h : Equation12505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12506_implies_Equation2 (G : Type*) [Magma G] (h : Equation12506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12507_implies_Equation2 (G : Type*) [Magma G] (h : Equation12507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12508_implies_Equation2 (G : Type*) [Magma G] (h : Equation12508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12510_implies_Equation2 (G : Type*) [Magma G] (h : Equation12510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12511_implies_Equation2 (G : Type*) [Magma G] (h : Equation12511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12512_implies_Equation2 (G : Type*) [Magma G] (h : Equation12512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12513_implies_Equation2 (G : Type*) [Magma G] (h : Equation12513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12515_implies_Equation2 (G : Type*) [Magma G] (h : Equation12515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12516_implies_Equation2 (G : Type*) [Magma G] (h : Equation12516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12517_implies_Equation2 (G : Type*) [Magma G] (h : Equation12517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12518_implies_Equation2 (G : Type*) [Magma G] (h : Equation12518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12520_implies_Equation2 (G : Type*) [Magma G] (h : Equation12520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12521_implies_Equation2 (G : Type*) [Magma G] (h : Equation12521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12522_implies_Equation2 (G : Type*) [Magma G] (h : Equation12522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12523_implies_Equation2 (G : Type*) [Magma G] (h : Equation12523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12524_implies_Equation2 (G : Type*) [Magma G] (h : Equation12524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12526_implies_Equation2 (G : Type*) [Magma G] (h : Equation12526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ X3) := superpose eq7 eq11
  have eq70 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = (X4 ◇ X5) := superpose eq22 eq22
  have eq183 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq70
  have eq305 (X0 X4 : G) : X0 = X4 := superpose eq7 eq183
  have eq498 (X0 : G) : sK0 ≠ X0 := superpose eq305 eq8
  subsumption eq498 eq305


@[equational_result]
theorem Equation12527_implies_Equation2 (G : Type*) [Magma G] (h : Equation12527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X4) ◇ X4) = (X1 ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq12
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq164 eq50


@[equational_result]
theorem Equation12528_implies_Equation2 (G : Type*) [Magma G] (h : Equation12528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (((X3 ◇ X4) ◇ X4) ◇ (X0 ◇ X4))) ◇ (X5 ◇ (((X3 ◇ X4) ◇ X4) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (((X3 ◇ X4) ◇ X4) ◇ (X0 ◇ X4))) ◇ X0)) = X5 := superpose eq7 eq9
  have eq14 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X0)) = X5 := superpose eq7 eq13
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq60 eq21


@[equational_result]
theorem Equation12529_implies_Equation2 (G : Type*) [Magma G] (h : Equation12529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 X5 : G) : ((X4 ◇ X5) ◇ X5) = (X1 ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq134 eq50


@[equational_result]
theorem Equation12531_implies_Equation2 (G : Type*) [Magma G] (h : Equation12531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12532_implies_Equation2 (G : Type*) [Magma G] (h : Equation12532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12533_implies_Equation2 (G : Type*) [Magma G] (h : Equation12533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12534_implies_Equation2 (G : Type*) [Magma G] (h : Equation12534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12536_implies_Equation2 (G : Type*) [Magma G] (h : Equation12536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12537_implies_Equation2 (G : Type*) [Magma G] (h : Equation12537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12538_implies_Equation2 (G : Type*) [Magma G] (h : Equation12538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12539_implies_Equation2 (G : Type*) [Magma G] (h : Equation12539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12541_implies_Equation2 (G : Type*) [Magma G] (h : Equation12541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12542_implies_Equation2 (G : Type*) [Magma G] (h : Equation12542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12543_implies_Equation2 (G : Type*) [Magma G] (h : Equation12543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12544_implies_Equation2 (G : Type*) [Magma G] (h : Equation12544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12546_implies_Equation2 (G : Type*) [Magma G] (h : Equation12546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12547_implies_Equation2 (G : Type*) [Magma G] (h : Equation12547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12548_implies_Equation2 (G : Type*) [Magma G] (h : Equation12548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12549_implies_Equation2 (G : Type*) [Magma G] (h : Equation12549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12550_implies_Equation2 (G : Type*) [Magma G] (h : Equation12550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12552_implies_Equation2 (G : Type*) [Magma G] (h : Equation12552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X7 : G) : (X1 ◇ (X0 ◇ (X7 ◇ X1))) = X7 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq128 eq41


@[equational_result]
theorem Equation12553_implies_Equation2 (G : Type*) [Magma G] (h : Equation12553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X0 ◇ (X7 ◇ X2))) = X7 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation12554_implies_Equation2 (G : Type*) [Magma G] (h : Equation12554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X7 : G) : (X1 ◇ (X0 ◇ (X7 ◇ X3))) = X7 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq51 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation12555_implies_Equation2 (G : Type*) [Magma G] (h : Equation12555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ (X7 ◇ (((X4 ◇ X5) ◇ X6) ◇ (X0 ◇ X6))))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : (X1 ◇ (X0 ◇ X0)) = X7 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation12556_implies_Equation2 (G : Type*) [Magma G] (h : Equation12556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X8 X9 : G) : (X1 ◇ (X0 ◇ (X8 ◇ X9))) = X8 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation12558_implies_Equation2 (G : Type*) [Magma G] (h : Equation12558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12559_implies_Equation2 (G : Type*) [Magma G] (h : Equation12559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12560_implies_Equation2 (G : Type*) [Magma G] (h : Equation12560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12561_implies_Equation2 (G : Type*) [Magma G] (h : Equation12561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12562_implies_Equation2 (G : Type*) [Magma G] (h : Equation12562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X1 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12564_implies_Equation2 (G : Type*) [Magma G] (h : Equation12564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12565_implies_Equation2 (G : Type*) [Magma G] (h : Equation12565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12566_implies_Equation2 (G : Type*) [Magma G] (h : Equation12566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12567_implies_Equation2 (G : Type*) [Magma G] (h : Equation12567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12568_implies_Equation2 (G : Type*) [Magma G] (h : Equation12568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X2 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12570_implies_Equation2 (G : Type*) [Magma G] (h : Equation12570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12571_implies_Equation2 (G : Type*) [Magma G] (h : Equation12571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12572_implies_Equation2 (G : Type*) [Magma G] (h : Equation12572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12573_implies_Equation2 (G : Type*) [Magma G] (h : Equation12573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12574_implies_Equation2 (G : Type*) [Magma G] (h : Equation12574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X3 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12576_implies_Equation2 (G : Type*) [Magma G] (h : Equation12576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12577_implies_Equation2 (G : Type*) [Magma G] (h : Equation12577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12578_implies_Equation2 (G : Type*) [Magma G] (h : Equation12578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12579_implies_Equation2 (G : Type*) [Magma G] (h : Equation12579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12580_implies_Equation2 (G : Type*) [Magma G] (h : Equation12580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12582_implies_Equation2 (G : Type*) [Magma G] (h : Equation12582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12583_implies_Equation2 (G : Type*) [Magma G] (h : Equation12583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12584_implies_Equation2 (G : Type*) [Magma G] (h : Equation12584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12585_implies_Equation2 (G : Type*) [Magma G] (h : Equation12585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12586_implies_Equation2 (G : Type*) [Magma G] (h : Equation12586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12587_implies_Equation2 (G : Type*) [Magma G] (h : Equation12587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X5 ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12793_implies_Equation2 (G : Type*) [Magma G] (h : Equation12793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12796_implies_Equation2 (G : Type*) [Magma G] (h : Equation12796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation12798_implies_Equation2 (G : Type*) [Magma G] (h : Equation12798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) = X2 := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq7 eq11
  have eq32 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq11
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) = X0 := superpose eq11 eq11
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq32 eq29
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X1) := superpose eq32 eq44
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) = X0 := superpose eq32 eq33
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq32 eq49
  have eq70 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq9 eq15
  have eq88 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq70 eq50
  have eq91 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq88 eq15
  have eq97 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq88 eq91
  have eq102 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) = X2 := superpose eq97 eq17
  have eq104 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X1) := superpose eq97 eq48
  have eq115 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq97 eq102
  have eq116 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq115 eq104
  have eq117 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq115 eq116
  have eq118 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq97 eq117
  have eq119 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq118 eq12
  have eq126 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq118 eq119
  have eq127 (X0 X1 : G) : X0 = X1 := superpose eq118 eq126
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq129 eq127


@[equational_result]
theorem Equation12799_implies_Equation2 (G : Type*) [Magma G] (h : Equation12799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation12800_implies_Equation2 (G : Type*) [Magma G] (h : Equation12800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12803_implies_Equation2 (G : Type*) [Magma G] (h : Equation12803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation12806_implies_Equation2 (G : Type*) [Magma G] (h : Equation12806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq45 eq11


@[equational_result]
theorem Equation12808_implies_Equation2 (G : Type*) [Magma G] (h : Equation12808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq11
  have eq117 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq216 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq216 eq117


@[equational_result]
theorem Equation12809_implies_Equation2 (G : Type*) [Magma G] (h : Equation12809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X2))) = X3 := superpose eq9 eq9
  have eq32 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq9
  have eq77 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2)) ◇ X1)) ◇ X0) = X0 := superpose eq32 eq11
  have eq89 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq7 eq77
  have eq111 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) := superpose eq89 eq32
  have eq141 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose eq89 eq111
  have eq215 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq141 eq10
  have eq216 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq141 eq7
  have eq219 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq141 eq10
  have eq259 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq32 eq219
  have eq264 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq259 eq215
  have eq272 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq264 eq216
  have eq275 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq272 eq89
  have eq290 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq272 eq275
  have eq293 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X2))) = X3 := superpose eq290 eq31
  have eq398 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X2)) = X3 := superpose eq290 eq293
  have eq399 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2) = X3 := superpose eq290 eq398
  have eq400 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X3 := superpose eq290 eq399
  have eq401 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq290 eq400
  have eq404 (X0 X2 : G) : X0 = X2 := superpose eq401 eq401
  have eq406 (X0 : G) : sK0 ≠ X0 := superpose eq404 eq8
  subsumption eq406 eq404


@[equational_result]
theorem Equation12810_implies_Equation2 (G : Type*) [Magma G] (h : Equation12810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation12812_implies_Equation2 (G : Type*) [Magma G] (h : Equation12812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq106 eq37


@[equational_result]
theorem Equation12813_implies_Equation2 (G : Type*) [Magma G] (h : Equation12813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation12814_implies_Equation2 (G : Type*) [Magma G] (h : Equation12814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) ◇ (((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) ◇ X0)) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X4)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X5)) := superpose eq10 eq9
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = X0 := superpose eq7 eq13
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq7
  have eq16 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq15 eq14
  have eq18 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq15 eq16
  have eq19 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq15 eq18
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq15 eq19
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation12816_implies_Equation2 (G : Type*) [Magma G] (h : Equation12816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq10
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq66 eq32


@[equational_result]
theorem Equation12818_implies_Equation2 (G : Type*) [Magma G] (h : Equation12818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation12821_implies_Equation2 (G : Type*) [Magma G] (h : Equation12821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation12822_implies_Equation2 (G : Type*) [Magma G] (h : Equation12822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation12824_implies_Equation2 (G : Type*) [Magma G] (h : Equation12824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq133 eq41


@[equational_result]
theorem Equation12825_implies_Equation2 (G : Type*) [Magma G] (h : Equation12825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12826_implies_Equation2 (G : Type*) [Magma G] (h : Equation12826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation12827_implies_Equation2 (G : Type*) [Magma G] (h : Equation12827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation12830_implies_Equation2 (G : Type*) [Magma G] (h : Equation12830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation12833_implies_Equation2 (G : Type*) [Magma G] (h : Equation12833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation12835_implies_Equation2 (G : Type*) [Magma G] (h : Equation12835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq9 eq9
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq11 eq14
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq62 eq52


@[equational_result]
theorem Equation12837_implies_Equation2 (G : Type*) [Magma G] (h : Equation12837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12840_implies_Equation2 (G : Type*) [Magma G] (h : Equation12840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation12843_implies_Equation2 (G : Type*) [Magma G] (h : Equation12843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq43 eq11


@[equational_result]
theorem Equation12845_implies_Equation2 (G : Type*) [Magma G] (h : Equation12845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq85 eq31


@[equational_result]
theorem Equation12846_implies_Equation2 (G : Type*) [Magma G] (h : Equation12846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) ◇ X3))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X4))) ◇ X4)))) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2))) = X1 := superpose eq7 eq17
  have eq36 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq19
  have eq83 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq36 eq17
  have eq89 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq36 eq7
  have eq95 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq36 eq83
  have eq269 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2)))) := superpose eq95 eq14
  have eq290 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq14 eq269
  have eq329 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq290 eq89
  have eq399 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq290 eq329
  have eq561 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X0))) := superpose eq290 eq9
  have eq576 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq7 eq561
  have eq598 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X2))) = X0 := superpose eq290 eq12
  have eq643 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq7 eq598
  have eq644 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq643 eq399
  have eq651 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq290 eq644
  have eq656 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X3))) = X1 := superpose eq651 eq12
  have eq870 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq651 eq576
  have eq914 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3))) = X1 := superpose eq651 eq656
  have eq1179 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq290 eq870
  have eq1183 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq1179 eq914
  have eq1377 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq1179 eq1183
  have eq1503 (X0 X2 : G) : X0 = X2 := superpose eq1377 eq1377
  have eq1508 (X0 : G) : sK0 ≠ X0 := superpose eq1503 eq8
  subsumption eq1508 eq1503


@[equational_result]
theorem Equation12847_implies_Equation2 (G : Type*) [Magma G] (h : Equation12847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation12849_implies_Equation2 (G : Type*) [Magma G] (h : Equation12849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq10
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq63 eq34


@[equational_result]
theorem Equation12851_implies_Equation2 (G : Type*) [Magma G] (h : Equation12851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation12853_implies_Equation2 (G : Type*) [Magma G] (h : Equation12853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq101 eq37


@[equational_result]
theorem Equation12855_implies_Equation2 (G : Type*) [Magma G] (h : Equation12855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation12858_implies_Equation2 (G : Type*) [Magma G] (h : Equation12858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq40 eq19


@[equational_result]
theorem Equation12859_implies_Equation2 (G : Type*) [Magma G] (h : Equation12859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation12861_implies_Equation2 (G : Type*) [Magma G] (h : Equation12861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq102 eq35


@[equational_result]
theorem Equation12862_implies_Equation2 (G : Type*) [Magma G] (h : Equation12862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = X1 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq43 eq26


@[equational_result]
theorem Equation12863_implies_Equation2 (G : Type*) [Magma G] (h : Equation12863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation12864_implies_Equation2 (G : Type*) [Magma G] (h : Equation12864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation12866_implies_Equation2 (G : Type*) [Magma G] (h : Equation12866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq10 eq7
  have eq26 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq15
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq160 eq73


@[equational_result]
theorem Equation12867_implies_Equation2 (G : Type*) [Magma G] (h : Equation12867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation12868_implies_Equation2 (G : Type*) [Magma G] (h : Equation12868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12870_implies_Equation2 (G : Type*) [Magma G] (h : Equation12870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1))) = X1 := superpose eq7 eq9
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq7 eq20
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq70 eq36


@[equational_result]
theorem Equation12872_implies_Equation2 (G : Type*) [Magma G] (h : Equation12872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12875_implies_Equation2 (G : Type*) [Magma G] (h : Equation12875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) ◇ X0)) ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation12876_implies_Equation2 (G : Type*) [Magma G] (h : Equation12876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12878_implies_Equation2 (G : Type*) [Magma G] (h : Equation12878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq116 eq47


@[equational_result]
theorem Equation12879_implies_Equation2 (G : Type*) [Magma G] (h : Equation12879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12880_implies_Equation2 (G : Type*) [Magma G] (h : Equation12880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X4 ◇ (X0 ◇ X5))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation12881_implies_Equation2 (G : Type*) [Magma G] (h : Equation12881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12885_implies_Equation2 (G : Type*) [Magma G] (h : Equation12885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12887_implies_Equation2 (G : Type*) [Magma G] (h : Equation12887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation12889_implies_Equation2 (G : Type*) [Magma G] (h : Equation12889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation12891_implies_Equation2 (G : Type*) [Magma G] (h : Equation12891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ ((X4 ◇ X1) ◇ (X1 ◇ X0))) = X4 := superpose eq7 eq10
  have eq40 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq25
  have eq84 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq40
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq7 eq84
  have eq323 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq323 eq173


@[equational_result]
theorem Equation12892_implies_Equation2 (G : Type*) [Magma G] (h : Equation12892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X3) ◇ X0)) ◇ ((X0 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X2))) = ((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X2) ◇ (((X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X2) ◇ ((X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X2)))) ◇ X0) = X3 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := superpose eq7 eq9
  have eq45 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := superpose eq12 eq7
  have eq82 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq12 eq13
  have eq87 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X2)) = X4 := superpose eq13 eq10
  have eq138 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq82 eq82
  have eq145 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) ◇ X0) = X1 := superpose eq82 eq10
  have eq162 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq82 eq138
  have eq166 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X0) = X1 := superpose eq82 eq145
  have eq223 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) = ((X0 ◇ ((((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) ◇ (((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2))) ◇ X1) := superpose eq7 eq166
  have eq225 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq10 eq166
  have eq229 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq82 eq166
  have eq237 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq166 eq13
  have eq240 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq166 eq13
  have eq253 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq166 eq7
  have eq259 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq82 eq229
  have eq266 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq162 eq237
  have eq269 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq10 eq240
  have eq272 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq269 eq266
  have eq275 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq269 eq259
  have eq279 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) = ((X0 ◇ X0) ◇ X1) := superpose eq272 eq223
  have eq280 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq272 eq225
  have eq281 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ X2))) = X1 := superpose eq279 eq19
  have eq346 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ ((X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1)))) ◇ ((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ ((X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))))))) = X3 := superpose eq12 eq281
  have eq352 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))))) = X2 := superpose eq13 eq281
  have eq377 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ ((X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1)))) ◇ ((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2)) ◇ (X3 ◇ X1)))) = X3 := superpose eq280 eq346
  have eq378 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2)) ◇ (X3 ◇ X1)))) = X3 := superpose eq45 eq377
  have eq382 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = X2 := superpose eq87 eq352
  have eq392 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := superpose eq382 eq162
  have eq395 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq382 eq166
  have eq408 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) := superpose eq382 eq253
  have eq413 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq382 eq269
  have eq430 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X2) ◇ X0) = X3 := superpose eq413 eq15
  have eq434 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq413 eq10
  have eq546 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X0) = X3 := superpose eq434 eq430
  have eq554 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq546 eq392
  have eq559 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := superpose eq554 eq7
  have eq561 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq554 eq275
  have eq562 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X2 ◇ X2)) ◇ X2) := superpose eq554 eq279
  have eq563 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X2))) = X1 := superpose eq554 eq281
  have eq567 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) ◇ (X3 ◇ X1)))) = X3 := superpose eq554 eq378
  have eq571 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X2 ◇ X2) ◇ X0) ◇ X0) := superpose eq554 eq408
  have eq581 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq554 eq561
  have eq583 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X2))) = X1 := superpose eq554 eq563
  have eq584 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2))) = X1 := superpose eq581 eq583
  have eq585 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X1 := superpose eq554 eq584
  have eq594 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X0)) ◇ (X1 ◇ (X3 ◇ X1)))) = X3 := superpose eq559 eq567
  have eq595 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1))) = X3 := superpose eq554 eq594
  have eq597 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = X3 := superpose eq571 eq595
  have eq599 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X1) = X3 := superpose eq395 eq597
  have eq600 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq599 eq562
  have eq606 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq600 eq585
  have eq613 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq600 eq606
  have eq614 (X0 X3 : G) : X0 = X3 := superpose eq613 eq613
  have eq625 (X0 : G) : sK0 ≠ X0 := superpose eq614 eq8
  subsumption eq625 eq614


@[equational_result]
theorem Equation12893_implies_Equation2 (G : Type*) [Magma G] (h : Equation12893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12895_implies_Equation2 (G : Type*) [Magma G] (h : Equation12895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq127 eq49


@[equational_result]
theorem Equation12896_implies_Equation2 (G : Type*) [Magma G] (h : Equation12896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X4))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq46 eq26


@[equational_result]
theorem Equation12897_implies_Equation2 (G : Type*) [Magma G] (h : Equation12897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation12898_implies_Equation2 (G : Type*) [Magma G] (h : Equation12898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12901_implies_Equation2 (G : Type*) [Magma G] (h : Equation12901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation12902_implies_Equation2 (G : Type*) [Magma G] (h : Equation12902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12906_implies_Equation2 (G : Type*) [Magma G] (h : Equation12906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation12908_implies_Equation2 (G : Type*) [Magma G] (h : Equation12908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq116 eq37


@[equational_result]
theorem Equation12909_implies_Equation2 (G : Type*) [Magma G] (h : Equation12909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3) ◇ X0)) ◇ ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq25 eq12


@[equational_result]
theorem Equation12910_implies_Equation2 (G : Type*) [Magma G] (h : Equation12910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12912_implies_Equation2 (G : Type*) [Magma G] (h : Equation12912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq140 eq41


@[equational_result]
theorem Equation12913_implies_Equation2 (G : Type*) [Magma G] (h : Equation12913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation12914_implies_Equation2 (G : Type*) [Magma G] (h : Equation12914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X4 ◇ (X4 ◇ X5))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation12915_implies_Equation2 (G : Type*) [Magma G] (h : Equation12915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12917_implies_Equation2 (G : Type*) [Magma G] (h : Equation12917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq118 eq41


@[equational_result]
theorem Equation12918_implies_Equation2 (G : Type*) [Magma G] (h : Equation12918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12919_implies_Equation2 (G : Type*) [Magma G] (h : Equation12919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12920_implies_Equation2 (G : Type*) [Magma G] (h : Equation12920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12922_implies_Equation2 (G : Type*) [Magma G] (h : Equation12922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq124 eq41


@[equational_result]
theorem Equation12923_implies_Equation2 (G : Type*) [Magma G] (h : Equation12923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq10 eq11
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation12924_implies_Equation2 (G : Type*) [Magma G] (h : Equation12924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation12925_implies_Equation2 (G : Type*) [Magma G] (h : Equation12925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12927_implies_Equation2 (G : Type*) [Magma G] (h : Equation12927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq163 eq67


@[equational_result]
theorem Equation12928_implies_Equation2 (G : Type*) [Magma G] (h : Equation12928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X3) ◇ X0)) ◇ ((X0 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation12929_implies_Equation2 (G : Type*) [Magma G] (h : Equation12929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation12930_implies_Equation2 (G : Type*) [Magma G] (h : Equation12930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12932_implies_Equation2 (G : Type*) [Magma G] (h : Equation12932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq110 eq40


@[equational_result]
theorem Equation12933_implies_Equation2 (G : Type*) [Magma G] (h : Equation12933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation12934_implies_Equation2 (G : Type*) [Magma G] (h : Equation12934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X4 ◇ (X5 ◇ X5))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation12935_implies_Equation2 (G : Type*) [Magma G] (h : Equation12935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12937_implies_Equation2 (G : Type*) [Magma G] (h : Equation12937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation12938_implies_Equation2 (G : Type*) [Magma G] (h : Equation12938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12939_implies_Equation2 (G : Type*) [Magma G] (h : Equation12939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12940_implies_Equation2 (G : Type*) [Magma G] (h : Equation12940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X5 ◇ (X6 ◇ X7))) ◇ X7))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation12941_implies_Equation2 (G : Type*) [Magma G] (h : Equation12941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation12944_implies_Equation2 (G : Type*) [Magma G] (h : Equation12944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation12947_implies_Equation2 (G : Type*) [Magma G] (h : Equation12947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation12949_implies_Equation2 (G : Type*) [Magma G] (h : Equation12949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq38 eq20


@[equational_result]
theorem Equation12950_implies_Equation2 (G : Type*) [Magma G] (h : Equation12950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ X4))) ◇ X4))) = X2 := superpose eq7 eq9
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4)) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4)) ◇ X5))) ◇ X5))) = X2 := superpose eq9 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) ◇ (((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) ◇ X4))) ◇ X4))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X4))) ◇ X4)))) = X2 := superpose eq7 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq14 eq7
  have eq41 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq34
  have eq46 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq41 eq7
  have eq55 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose eq41 eq7
  have eq58 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq41 eq55
  have eq91 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq41 eq46
  have eq240 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) := superpose eq7 eq10
  have eq275 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq91 eq58
  have eq304 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq275 eq46
  have eq647 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3)) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3)) ◇ X4))) ◇ X4))) = X2 := superpose eq304 eq11
  have eq648 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X3))) ◇ X3))) = X0 := superpose eq304 eq13
  have eq677 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X3))) ◇ X3)) = X0 := superpose eq7 eq240
  have eq732 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq677 eq648
  have eq734 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ ((((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ X4))) ◇ X4))) = X2 := superpose eq732 eq647
  have eq1041 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ ((((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ X4))) ◇ X4)) = X2 := superpose eq732 eq734
  have eq1042 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq732 eq1041
  have eq1043 (X0 X1 : G) : X0 = X1 := superpose eq275 eq1042
  have eq1051 (X0 : G) : sK0 ≠ X0 := superpose eq1043 eq8
  subsumption eq1051 eq1043


@[equational_result]
theorem Equation12951_implies_Equation2 (G : Type*) [Magma G] (h : Equation12951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation12954_implies_Equation2 (G : Type*) [Magma G] (h : Equation12954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation12957_implies_Equation2 (G : Type*) [Magma G] (h : Equation12957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq53 eq12


@[equational_result]
theorem Equation12959_implies_Equation2 (G : Type*) [Magma G] (h : Equation12959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq9
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq33 eq23


@[equational_result]
theorem Equation12961_implies_Equation2 (G : Type*) [Magma G] (h : Equation12961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12963_implies_Equation2 (G : Type*) [Magma G] (h : Equation12963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation12964_implies_Equation2 (G : Type*) [Magma G] (h : Equation12964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X3) = (X1 ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X3) ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) ◇ (X0 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq428 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1))) ◇ (X2 ◇ X0))) = X1 := superpose eq25 eq7
  have eq606 (X0 X1 : G) : X0 = X1 := superpose eq10 eq428
  have eq707 (X0 : G) : sK0 ≠ X0 := superpose eq606 eq8
  subsumption eq707 eq606


@[equational_result]
theorem Equation12965_implies_Equation2 (G : Type*) [Magma G] (h : Equation12965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12967_implies_Equation2 (G : Type*) [Magma G] (h : Equation12967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq31 eq13


@[equational_result]
theorem Equation12969_implies_Equation2 (G : Type*) [Magma G] (h : Equation12969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12973_implies_Equation2 (G : Type*) [Magma G] (h : Equation12973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation12975_implies_Equation2 (G : Type*) [Magma G] (h : Equation12975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation12976_implies_Equation2 (G : Type*) [Magma G] (h : Equation12976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4))))) = X2 := superpose eq7 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation12977_implies_Equation2 (G : Type*) [Magma G] (h : Equation12977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation12978_implies_Equation2 (G : Type*) [Magma G] (h : Equation12978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12981_implies_Equation2 (G : Type*) [Magma G] (h : Equation12981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq55 eq11


@[equational_result]
theorem Equation12984_implies_Equation2 (G : Type*) [Magma G] (h : Equation12984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation12986_implies_Equation2 (G : Type*) [Magma G] (h : Equation12986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation12987_implies_Equation2 (G : Type*) [Magma G] (h : Equation12987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2)) := superpose eq10 eq7
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq33 eq7
  have eq42 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq33 eq9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2)) = (X0 ◇ X1) := superpose eq33 eq17
  have eq59 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq33 eq42
  have eq60 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq33 eq45
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq41 eq60
  have eq64 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq61 eq59
  have eq70 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X3)) = X2 := superpose eq61 eq64
  have eq71 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq61 eq70
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq71 eq71
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq74 eq72


@[equational_result]
theorem Equation12988_implies_Equation2 (G : Type*) [Magma G] (h : Equation12988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation12991_implies_Equation2 (G : Type*) [Magma G] (h : Equation12991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq60 eq11


@[equational_result]
theorem Equation12993_implies_Equation2 (G : Type*) [Magma G] (h : Equation12993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12994_implies_Equation2 (G : Type*) [Magma G] (h : Equation12994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12996_implies_Equation2 (G : Type*) [Magma G] (h : Equation12996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12997_implies_Equation2 (G : Type*) [Magma G] (h : Equation12997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12998_implies_Equation2 (G : Type*) [Magma G] (h : Equation12998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13000_implies_Equation2 (G : Type*) [Magma G] (h : Equation13000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation13002_implies_Equation2 (G : Type*) [Magma G] (h : Equation13002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation13004_implies_Equation2 (G : Type*) [Magma G] (h : Equation13004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13005_implies_Equation2 (G : Type*) [Magma G] (h : Equation13005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13006_implies_Equation2 (G : Type*) [Magma G] (h : Equation13006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13008_implies_Equation2 (G : Type*) [Magma G] (h : Equation13008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13009_implies_Equation2 (G : Type*) [Magma G] (h : Equation13009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13010_implies_Equation2 (G : Type*) [Magma G] (h : Equation13010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13012_implies_Equation2 (G : Type*) [Magma G] (h : Equation13012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13013_implies_Equation2 (G : Type*) [Magma G] (h : Equation13013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13014_implies_Equation2 (G : Type*) [Magma G] (h : Equation13014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13015_implies_Equation2 (G : Type*) [Magma G] (h : Equation13015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13017_implies_Equation2 (G : Type*) [Magma G] (h : Equation13017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : X0 = X1 := superpose eq7 eq9
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq15 eq11


@[equational_result]
theorem Equation13019_implies_Equation2 (G : Type*) [Magma G] (h : Equation13019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation13021_implies_Equation2 (G : Type*) [Magma G] (h : Equation13021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ ((((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = (((((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)) ◇ ((((((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X4 ◇ X1)) ◇ ((((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)))) := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) = (((((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X4 ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ ((((((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X4 ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ ((((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X4 ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))))) := superpose eq9 eq9
  have eq44 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X4 ◇ X0)) = (((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ ((((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))) := superpose eq9 eq10
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) = (((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X4 ◇ X0)) := superpose eq31 eq44
  have eq48 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) = ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ (((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))))) := superpose eq47 eq34
  have eq51 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) = (X0 ◇ ((X0 ◇ (X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) ◇ X0)) := superpose eq9 eq48
  have eq52 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = ((((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq7 eq51
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq52 eq9
  have eq71 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = X2 := superpose eq10 eq17
  have eq76 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq17 eq7
  have eq118 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq17 eq55
  have eq132 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq118 eq7
  have eq155 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq132 eq71
  have eq156 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq155 eq76
  have eq164 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq156 eq17
  have eq169 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq156 eq164
  have eq170 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq169 eq118
  have eq174 (X0 X1 : G) : X0 = X1 := superpose eq169 eq170
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq174 eq8
  subsumption eq176 eq174


@[equational_result]
theorem Equation13023_implies_Equation2 (G : Type*) [Magma G] (h : Equation13023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13025_implies_Equation2 (G : Type*) [Magma G] (h : Equation13025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X3))) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X3))) = (X5 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := superpose eq7 eq10
  have eq31 (X0 X1 X5 : G) : (X5 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) = X1 := superpose eq22 eq20
  have eq108 (X0 X3 : G) : X0 = X3 := superpose eq22 eq31
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq125 eq108


@[equational_result]
theorem Equation13026_implies_Equation2 (G : Type*) [Magma G] (h : Equation13026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) ◇ X0)) ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq10 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) = X1 := superpose eq10 eq7
  have eq26 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose eq10 eq20
  have eq60 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq21 eq21
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq10 eq26
  have eq81 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) = X1 := superpose eq10 eq26
  have eq89 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (X2 ◇ (((X2 ◇ X1) ◇ X0) ◇ X2)) := superpose eq10 eq60
  have eq206 (X0 X1 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq80 eq7
  have eq218 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq60 eq206
  have eq219 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq7 eq218
  have eq258 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := superpose eq14 eq9
  have eq292 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq7 eq81
  have eq293 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq14 eq81
  have eq296 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq10 eq81
  have eq340 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq60 eq293
  have eq347 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := superpose eq340 eq258
  have eq357 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X1 ◇ X0)))))) = X2 := superpose eq292 eq347
  have eq363 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) := superpose eq89 eq296
  have eq364 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) := superpose eq60 eq363
  have eq365 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq10 eq364
  have eq436 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0))) := superpose eq15 eq81
  have eq492 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)))) := superpose eq60 eq436
  have eq493 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := superpose eq7 eq492
  have eq497 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X1 ◇ X0)))))) = X2 := superpose eq493 eq357
  have eq501 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq493 eq219
  have eq581 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X1 ◇ X0)))))) = X2 := superpose eq493 eq497
  have eq582 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ X0)))))) = X2 := superpose eq493 eq581
  have eq583 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ X0)))))) = X2 := superpose eq493 eq582
  have eq584 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ X0)))))) = X2 := superpose eq493 eq583
  have eq585 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ X0)))))) = X2 := superpose eq340 eq584
  have eq586 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)))))) ◇ X0)))))) = X2 := superpose eq292 eq585
  have eq587 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)))))) ◇ X0)))))) = X2 := superpose eq493 eq586
  have eq588 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))))))) ◇ X0)))))) = X2 := superpose eq89 eq587
  have eq589 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))))))) ◇ X0)))))) = X2 := superpose eq60 eq588
  have eq590 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) ◇ X0)))))) = X2 := superpose eq10 eq589
  have eq591 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0)))))) = X2 := superpose eq365 eq590
  have eq621 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq340 eq501
  have eq622 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))))) = X0 := superpose eq292 eq621
  have eq623 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))) = X0 := superpose eq493 eq622
  have eq624 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq365 eq623
  have eq625 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq624 eq26
  have eq703 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq624 eq625
  have eq704 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0))))) = X2 := superpose eq703 eq591
  have eq737 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0)))) = X2 := superpose eq703 eq704
  have eq738 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0))) = X2 := superpose eq703 eq737
  have eq739 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0)) = X2 := superpose eq703 eq738
  have eq740 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X2 := superpose eq703 eq739
  have eq741 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X2 := superpose eq703 eq740
  have eq742 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq703 eq741
  have eq743 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq703 eq742
  have eq744 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq703 eq743
  have eq745 (X0 X3 : G) : X0 = X3 := superpose eq744 eq744
  have eq750 (X0 : G) : sK0 ≠ X0 := superpose eq745 eq8
  subsumption eq750 eq745


@[equational_result]
theorem Equation13027_implies_Equation2 (G : Type*) [Magma G] (h : Equation13027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13029_implies_Equation2 (G : Type*) [Magma G] (h : Equation13029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation13030_implies_Equation2 (G : Type*) [Magma G] (h : Equation13030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation13031_implies_Equation2 (G : Type*) [Magma G] (h : Equation13031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation13032_implies_Equation2 (G : Type*) [Magma G] (h : Equation13032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13034_implies_Equation2 (G : Type*) [Magma G] (h : Equation13034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)))) ◇ X0)) = X1 := superpose eq9 eq7
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))) = X1 := superpose eq25 eq10
  have eq73 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq67 eq29
  have eq84 (X0 X2 : G) : X0 = X2 := superpose eq73 eq73
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq120 eq84


@[equational_result]
theorem Equation13036_implies_Equation2 (G : Type*) [Magma G] (h : Equation13036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13038_implies_Equation2 (G : Type*) [Magma G] (h : Equation13038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13039_implies_Equation2 (G : Type*) [Magma G] (h : Equation13039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13040_implies_Equation2 (G : Type*) [Magma G] (h : Equation13040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13042_implies_Equation2 (G : Type*) [Magma G] (h : Equation13042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13043_implies_Equation2 (G : Type*) [Magma G] (h : Equation13043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13044_implies_Equation2 (G : Type*) [Magma G] (h : Equation13044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13046_implies_Equation2 (G : Type*) [Magma G] (h : Equation13046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13047_implies_Equation2 (G : Type*) [Magma G] (h : Equation13047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13048_implies_Equation2 (G : Type*) [Magma G] (h : Equation13048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13049_implies_Equation2 (G : Type*) [Magma G] (h : Equation13049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13051_implies_Equation2 (G : Type*) [Magma G] (h : Equation13051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = (X4 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X4)) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X4 ◇ (X3 ◇ X2)))) ◇ X3) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) = ((X0 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X0) := superpose eq9 eq9
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X2 := superpose eq22 eq21
  have eq45 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)))))) = X2 := superpose eq22 eq7
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq29
  have eq62 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)))) ◇ X1) = (X3 ◇ (X0 ◇ X3)) := superpose eq29 eq9
  have eq68 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X3 ◇ ((X3 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1)) ◇ X3)) := superpose eq7 eq14
  have eq107 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X4 ◇ ((X4 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ X4))) := superpose eq14 eq29
  have eq135 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq52 eq52
  have eq150 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X2 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X2)) := superpose eq52 eq9
  have eq154 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := superpose eq52 eq29
  have eq165 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq68 eq150
  have eq166 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq165 eq135
  have eq167 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose eq52 eq166
  have eq283 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq167 eq22
  have eq284 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq167 eq23
  have eq288 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq167 eq7
  have eq292 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq167 eq9
  have eq293 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq167 eq7
  have eq310 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq288 eq292
  have eq311 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq310 eq293
  have eq312 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq311 eq283
  have eq319 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq312 eq284
  have eq331 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq319 eq7
  have eq370 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ X3) = (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq331 eq107
  have eq413 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq331 eq370
  have eq416 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0))))) ◇ X1) = (X3 ◇ (X0 ◇ X3)) := superpose eq413 eq62
  have eq422 (X0 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X3)) := superpose eq22 eq416
  have eq428 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq422 eq154
  have eq433 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq319 eq428
  have eq434 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq331 eq433
  have eq435 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)))) = X2 := superpose eq434 eq45
  have eq455 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0) = X2 := superpose eq434 eq435
  have eq456 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq434 eq455
  have eq457 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq434 eq456
  have eq458 (X0 X3 : G) : X0 = X3 := superpose eq457 eq457
  have eq460 (X0 : G) : sK0 ≠ X0 := superpose eq458 eq8
  subsumption eq460 eq458


@[equational_result]
theorem Equation13053_implies_Equation2 (G : Type*) [Magma G] (h : Equation13053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation13055_implies_Equation2 (G : Type*) [Magma G] (h : Equation13055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13056_implies_Equation2 (G : Type*) [Magma G] (h : Equation13056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13057_implies_Equation2 (G : Type*) [Magma G] (h : Equation13057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13059_implies_Equation2 (G : Type*) [Magma G] (h : Equation13059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13060_implies_Equation2 (G : Type*) [Magma G] (h : Equation13060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13061_implies_Equation2 (G : Type*) [Magma G] (h : Equation13061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13063_implies_Equation2 (G : Type*) [Magma G] (h : Equation13063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13064_implies_Equation2 (G : Type*) [Magma G] (h : Equation13064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13065_implies_Equation2 (G : Type*) [Magma G] (h : Equation13065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13066_implies_Equation2 (G : Type*) [Magma G] (h : Equation13066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13068_implies_Equation2 (G : Type*) [Magma G] (h : Equation13068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation13069_implies_Equation2 (G : Type*) [Magma G] (h : Equation13069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation13070_implies_Equation2 (G : Type*) [Magma G] (h : Equation13070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation13071_implies_Equation2 (G : Type*) [Magma G] (h : Equation13071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13073_implies_Equation2 (G : Type*) [Magma G] (h : Equation13073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13074_implies_Equation2 (G : Type*) [Magma G] (h : Equation13074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13075_implies_Equation2 (G : Type*) [Magma G] (h : Equation13075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13076_implies_Equation2 (G : Type*) [Magma G] (h : Equation13076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13078_implies_Equation2 (G : Type*) [Magma G] (h : Equation13078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13079_implies_Equation2 (G : Type*) [Magma G] (h : Equation13079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13080_implies_Equation2 (G : Type*) [Magma G] (h : Equation13080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13081_implies_Equation2 (G : Type*) [Magma G] (h : Equation13081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13083_implies_Equation2 (G : Type*) [Magma G] (h : Equation13083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13084_implies_Equation2 (G : Type*) [Magma G] (h : Equation13084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13085_implies_Equation2 (G : Type*) [Magma G] (h : Equation13085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13086_implies_Equation2 (G : Type*) [Magma G] (h : Equation13086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13088_implies_Equation2 (G : Type*) [Magma G] (h : Equation13088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13089_implies_Equation2 (G : Type*) [Magma G] (h : Equation13089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13090_implies_Equation2 (G : Type*) [Magma G] (h : Equation13090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13091_implies_Equation2 (G : Type*) [Magma G] (h : Equation13091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13092_implies_Equation2 (G : Type*) [Magma G] (h : Equation13092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13094_implies_Equation2 (G : Type*) [Magma G] (h : Equation13094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3)) := superpose eq7 eq10
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq13
  have eq32 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose eq30 eq7
  have eq40 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq30 eq32
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq75 eq73


@[equational_result]
theorem Equation13095_implies_Equation2 (G : Type*) [Magma G] (h : Equation13095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation13096_implies_Equation2 (G : Type*) [Magma G] (h : Equation13096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq59 eq13


@[equational_result]
theorem Equation13098_implies_Equation2 (G : Type*) [Magma G] (h : Equation13098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ X3))) ◇ X3) ◇ ((X4 ◇ X0) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) ◇ X3))) ◇ X3))) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) = (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2)) ◇ ((X4 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2)))) := superpose eq7 eq9
  have eq55 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0) = (((X1 ◇ X0) ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X4 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0) ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)))) := superpose eq10 eq9
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0) = (((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0))) := superpose eq10 eq7
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose eq10 eq56
  have eq66 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X4 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq65 eq55
  have eq70 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0) = (((X1 ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)))) := superpose eq10 eq66
  have eq75 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)) = ((X0 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X5 ◇ (((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0)))) ◇ (X0 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0))) ◇ X0))))) := superpose eq10 eq66
  have eq83 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ X5))) ◇ X5) ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ X5))) ◇ X5) ◇ X5))) ◇ X5) ◇ (X0 ◇ ((X1 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ X5))) ◇ X5) ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ X5))) ◇ X5) ◇ X5))) ◇ X5))) = X5 := superpose eq66 eq10
  have eq87 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq65 eq70
  have eq123 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = ((X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) ◇ (((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))))) := superpose eq9 eq87
  have eq132 (X0 X1 X2 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) = X0 := superpose eq87 eq9
  have eq146 (X0 X1 X2 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq132
  have eq203 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) = (((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)))) := superpose eq146 eq14
  have eq222 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq146 eq87
  have eq223 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = ((X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq203 eq123
  have eq225 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) := superpose eq87 eq222
  have eq294 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) = ((((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)))) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) := superpose eq9 eq225
  have eq345 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) = (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) := superpose eq203 eq294
  have eq346 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))) = X0 := superpose eq9 eq345
  have eq347 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq346 eq223
  have eq352 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = X2 := superpose eq7 eq347
  have eq353 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X0) = X2 := superpose eq352 eq9
  have eq430 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq353 eq65
  have eq432 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq353 eq430
  have eq470 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ X5))) ◇ X5) ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ X5))) ◇ X5) ◇ X5))) ◇ X5) ◇ (X0 ◇ ((X1 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ X5))) ◇ X5) ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ X5))) ◇ X5) ◇ X5))) ◇ X5))) = X5 := superpose eq432 eq83
  have eq505 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0)) ◇ X0)) = ((X0 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0)) ◇ X0))) ◇ ((X5 ◇ (((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0)) ◇ X0)))) ◇ (X0 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0)) ◇ X0))))) := superpose eq432 eq75
  have eq760 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ X5))) ◇ X5) ◇ X5)) ◇ X5) ◇ (X0 ◇ ((X1 ◇ (((X2 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ X5))) ◇ X5) ◇ X5)) ◇ X5))) = X5 := superpose eq432 eq470
  have eq761 (X0 X1 X5 : G) : (((X1 ◇ X5) ◇ X5) ◇ (X0 ◇ ((X1 ◇ X5) ◇ X5))) = X5 := superpose eq432 eq760
  have eq762 (X0 X5 : G) : (X5 ◇ (X0 ◇ X5)) = X5 := superpose eq432 eq761
  have eq886 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X5 ◇ (((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq432 eq505
  have eq887 (X0 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X0) = ((X0 ◇ ((X4 ◇ X3) ◇ X0)) ◇ ((X5 ◇ (((X4 ◇ X3) ◇ X0) ◇ ((X4 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X4 ◇ X3) ◇ X0)))) := superpose eq432 eq886
  have eq888 (X0 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X0) = (X0 ◇ ((X5 ◇ (((X4 ◇ X3) ◇ X0) ◇ ((X4 ◇ X3) ◇ X0))) ◇ X0)) := superpose eq762 eq887
  have eq889 (X0 X3 X4 : G) : ((X4 ◇ X3) ◇ X0) = X0 := superpose eq762 eq888
  have eq890 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq889 eq7
  have eq919 (X0 X2 : G) : X0 = X2 := superpose eq890 eq890
  have eq921 (X0 : G) : sK0 ≠ X0 := superpose eq919 eq8
  subsumption eq921 eq919


@[equational_result]
theorem Equation13099_implies_Equation2 (G : Type*) [Magma G] (h : Equation13099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X3)) ◇ X4) = (((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2) ◇ X0)) ◇ X1) ◇ ((X5 ◇ (((X4 ◇ (X0 ◇ X3)) ◇ X4) ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2))) ◇ X5)) := superpose eq9 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2) ◇ X3))) ◇ X1) ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = (((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) ◇ X1) ◇ (X0 ◇ ((X4 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X4))) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) ◇ X1) ◇ X3) := superpose eq7 eq16
  have eq24 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) ◇ X2) = X0 := superpose eq7 eq20
  have eq35 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2) ◇ X3)) ◇ X1) ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq24 eq13
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X3)) ◇ X4) = (((X1 ◇ X0) ◇ X1) ◇ ((X5 ◇ (((X4 ◇ (X0 ◇ X3)) ◇ X4) ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2))) ◇ X5)) := superpose eq24 eq11
  have eq38 (X0 X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X1) ◇ ((X4 ◇ X0) ◇ X4)) = X3 := superpose eq24 eq35
  have eq43 (X0 X3 X4 : G) : ((X4 ◇ (X0 ◇ X3)) ◇ X4) = X0 := superpose eq38 eq36
  have eq44 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq43 eq7
  have eq55 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X0 := superpose eq44 eq43
  have eq59 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq44 eq55
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq59 eq59
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq65 eq60


@[equational_result]
theorem Equation13100_implies_Equation2 (G : Type*) [Magma G] (h : Equation13100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq61 eq12


@[equational_result]
theorem Equation13103_implies_Equation2 (G : Type*) [Magma G] (h : Equation13103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13104_implies_Equation2 (G : Type*) [Magma G] (h : Equation13104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation13106_implies_Equation2 (G : Type*) [Magma G] (h : Equation13106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq9
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq189 eq73


@[equational_result]
theorem Equation13107_implies_Equation2 (G : Type*) [Magma G] (h : Equation13107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation13108_implies_Equation2 (G : Type*) [Magma G] (h : Equation13108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X4 ◇ (X0 ◇ (X0 ◇ X5))) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13109_implies_Equation2 (G : Type*) [Magma G] (h : Equation13109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation13111_implies_Equation2 (G : Type*) [Magma G] (h : Equation13111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ ((X2 ◇ (((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ (X5 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3))))))) ◇ (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ (X5 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3))))))))) = X5 := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X3) = ((X1 ◇ X0) ◇ ((X5 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (((X4 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) ◇ X2) = (X2 ◇ ((X5 ◇ (((X3 ◇ (((X4 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) ◇ X2) ◇ ((X4 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1)) ◇ X2))) ◇ X2)) := superpose eq9 eq9
  have eq130 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq16 eq16
  have eq170 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := superpose eq7 eq130
  have eq171 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = (X4 ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1)) ◇ X2)) := superpose eq9 eq130
  have eq267 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X1) ◇ X2) = (X2 ◇ ((X5 ◇ (((X3 ◇ X1) ◇ X2) ◇ ((X4 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1)) ◇ X2))) ◇ X2)) := superpose eq170 eq20
  have eq272 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ X1) ◇ X2) = (X2 ◇ ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2)) ◇ X2)) := superpose eq171 eq267
  have eq275 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ X2) := superpose eq170 eq272
  have eq278 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq275 eq9
  have eq298 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq7 eq278
  have eq299 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq298 eq7
  have eq312 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))))) ◇ (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))))))) = X5 := superpose eq299 eq12
  have eq393 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))))) ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3))))))) = X5 := superpose eq299 eq312
  have eq394 (X0 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3))))) ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))))) = X5 := superpose eq299 eq393
  have eq395 (X0 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3))))) = X5 := superpose eq299 eq394
  have eq396 (X0 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X3)))) = X5 := superpose eq299 eq395
  have eq397 (X0 X3 X5 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X3))) = X5 := superpose eq299 eq396
  have eq398 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X3)) = X5 := superpose eq299 eq397
  have eq399 (X3 X5 : G) : (X3 ◇ X3) = X5 := superpose eq299 eq398
  have eq414 (X0 X1 : G) : X0 = X1 := superpose eq299 eq399
  have eq419 (X0 : G) : sK0 ≠ X0 := superpose eq414 eq8
  subsumption eq419 eq414


@[equational_result]
theorem Equation13113_implies_Equation2 (G : Type*) [Magma G] (h : Equation13113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation13115_implies_Equation2 (G : Type*) [Magma G] (h : Equation13115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X3 := superpose eq9 eq7
  have eq23 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq9 eq17
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq117 eq55


@[equational_result]
theorem Equation13117_implies_Equation2 (G : Type*) [Magma G] (h : Equation13117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq61 eq12


@[equational_result]
theorem Equation13121_implies_Equation2 (G : Type*) [Magma G] (h : Equation13121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation13123_implies_Equation2 (G : Type*) [Magma G] (h : Equation13123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq9
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq164 eq73


@[equational_result]
theorem Equation13124_implies_Equation2 (G : Type*) [Magma G] (h : Equation13124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ X0) ◇ X4)) = X2 := superpose eq7 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq44 eq35


@[equational_result]
theorem Equation13125_implies_Equation2 (G : Type*) [Magma G] (h : Equation13125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X4 ◇ (X0 ◇ (X1 ◇ X5))) ◇ X5))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X4)))) = (X1 ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X5 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X4))))) ◇ X4)) = X3 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4)) = X3 := superpose eq11 eq16
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq26 eq9
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq27 eq27
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq45 eq32


@[equational_result]
theorem Equation13126_implies_Equation2 (G : Type*) [Magma G] (h : Equation13126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation13128_implies_Equation2 (G : Type*) [Magma G] (h : Equation13128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq54 eq23


@[equational_result]
theorem Equation13129_implies_Equation2 (G : Type*) [Magma G] (h : Equation13129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation13130_implies_Equation2 (G : Type*) [Magma G] (h : Equation13130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation13134_implies_Equation2 (G : Type*) [Magma G] (h : Equation13134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation13137_implies_Equation2 (G : Type*) [Magma G] (h : Equation13137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13138_implies_Equation2 (G : Type*) [Magma G] (h : Equation13138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation13140_implies_Equation2 (G : Type*) [Magma G] (h : Equation13140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq9 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation13141_implies_Equation2 (G : Type*) [Magma G] (h : Equation13141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation13142_implies_Equation2 (G : Type*) [Magma G] (h : Equation13142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X4 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13143_implies_Equation2 (G : Type*) [Magma G] (h : Equation13143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation13145_implies_Equation2 (G : Type*) [Magma G] (h : Equation13145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation13146_implies_Equation2 (G : Type*) [Magma G] (h : Equation13146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation13147_implies_Equation2 (G : Type*) [Magma G] (h : Equation13147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation13148_implies_Equation2 (G : Type*) [Magma G] (h : Equation13148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13150_implies_Equation2 (G : Type*) [Magma G] (h : Equation13150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq31 eq16


@[equational_result]
theorem Equation13151_implies_Equation2 (G : Type*) [Magma G] (h : Equation13151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq53 eq17


@[equational_result]
theorem Equation13152_implies_Equation2 (G : Type*) [Magma G] (h : Equation13152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X3))))) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq142 eq50


@[equational_result]
theorem Equation13153_implies_Equation2 (G : Type*) [Magma G] (h : Equation13153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13155_implies_Equation2 (G : Type*) [Magma G] (h : Equation13155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation13156_implies_Equation2 (G : Type*) [Magma G] (h : Equation13156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X2) ◇ (X4 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13157_implies_Equation2 (G : Type*) [Magma G] (h : Equation13157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation13158_implies_Equation2 (G : Type*) [Magma G] (h : Equation13158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13160_implies_Equation2 (G : Type*) [Magma G] (h : Equation13160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ X4))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X5)))) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X4 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X4)) := superpose eq7 eq10
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq13
  have eq35 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X5)))) ◇ X0) = X4 := superpose eq34 eq11
  have eq40 (X0 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ (X5 ◇ X5))) ◇ X0) = X4 := superpose eq34 eq35
  have eq41 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X5)) ◇ X0) = X4 := superpose eq34 eq40
  have eq42 (X0 X4 X5 : G) : ((X5 ◇ X5) ◇ X0) = X4 := superpose eq34 eq41
  have eq43 (X0 X4 X5 : G) : (X5 ◇ X0) = X4 := superpose eq34 eq42
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation13161_implies_Equation2 (G : Type*) [Magma G] (h : Equation13161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation13162_implies_Equation2 (G : Type*) [Magma G] (h : Equation13162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X4 ◇ (X0 ◇ (X5 ◇ X5))) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13163_implies_Equation2 (G : Type*) [Magma G] (h : Equation13163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13165_implies_Equation2 (G : Type*) [Magma G] (h : Equation13165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation13166_implies_Equation2 (G : Type*) [Magma G] (h : Equation13166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13167_implies_Equation2 (G : Type*) [Magma G] (h : Equation13167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation13168_implies_Equation2 (G : Type*) [Magma G] (h : Equation13168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X5 ◇ (X0 ◇ (X6 ◇ X7))) ◇ X7))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13169_implies_Equation2 (G : Type*) [Magma G] (h : Equation13169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13171_implies_Equation2 (G : Type*) [Magma G] (h : Equation13171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X2 := superpose eq10 eq9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X3) ◇ X0)) ◇ (((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X3) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X3) ◇ X0)))) = X3 := superpose eq7 eq13
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0))) = X1 := superpose eq10 eq7
  have eq25 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq10 eq13
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X1 := superpose eq10 eq21
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq25
  have eq30 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq29 eq7
  have eq32 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)))) = X3 := superpose eq29 eq15
  have eq38 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X1 := superpose eq29 eq28
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq30 eq38
  have eq54 (X0 X2 X3 : G) : ((((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0))) = X3 := superpose eq52 eq32
  have eq65 (X0 X2 X3 : G) : ((((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0)) = X3 := superpose eq52 eq54
  have eq66 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq52 eq65
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq66 eq66
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq73 eq71


@[equational_result]
theorem Equation13173_implies_Equation2 (G : Type*) [Magma G] (h : Equation13173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation13175_implies_Equation2 (G : Type*) [Magma G] (h : Equation13175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq7 eq10
  have eq28 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) = X2 := superpose eq10 eq7
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)))) = X2 := superpose eq25 eq25
  have eq73 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = X2 := superpose eq10 eq25
  have eq109 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X1) := superpose eq28 eq28
  have eq131 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) = X2 := superpose eq109 eq69
  have eq170 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq73 eq131
  have eq171 (X0 X3 : G) : X0 = X3 := superpose eq7 eq170
  have eq262 (X0 : G) : sK0 ≠ X0 := superpose eq171 eq8
  subsumption eq262 eq171


@[equational_result]
theorem Equation13176_implies_Equation2 (G : Type*) [Magma G] (h : Equation13176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) = (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) := superpose eq10 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) = X2 := superpose eq10 eq7
  have eq26 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose eq10 eq20
  have eq52 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := superpose eq21 eq21
  have eq90 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X3) = X0 := superpose eq21 eq52
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) = X1 := superpose eq52 eq7
  have eq113 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3)) = X2 := superpose eq52 eq7
  have eq141 (X0 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) = X2 := superpose eq104 eq19
  have eq144 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq90 eq113
  have eq145 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq144 eq7
  have eq208 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq145 eq26
  have eq211 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq208 eq141
  have eq215 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq208 eq211
  have eq217 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq215 eq208
  have eq255 (X0 X1 : G) : X0 = X1 := superpose eq215 eq217
  have eq260 (X0 : G) : sK0 ≠ X0 := superpose eq255 eq8
  subsumption eq260 eq255


@[equational_result]
theorem Equation13177_implies_Equation2 (G : Type*) [Magma G] (h : Equation13177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation13180_implies_Equation2 (G : Type*) [Magma G] (h : Equation13180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq11
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) = X2 := superpose eq10 eq7
  have eq153 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq25 eq25
  have eq155 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq13 eq25
  have eq175 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq153 eq7
  have eq484 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq155 eq175
  have eq589 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq155 eq484
  have eq590 (X0 X3 : G) : X0 = X3 := superpose eq589 eq589
  have eq592 (X0 : G) : sK0 ≠ X0 := superpose eq590 eq8
  subsumption eq592 eq590


@[equational_result]
theorem Equation13181_implies_Equation2 (G : Type*) [Magma G] (h : Equation13181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation13183_implies_Equation2 (G : Type*) [Magma G] (h : Equation13183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation13184_implies_Equation2 (G : Type*) [Magma G] (h : Equation13184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation13185_implies_Equation2 (G : Type*) [Magma G] (h : Equation13185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X4))) = (X1 ◇ ((X2 ◇ X0) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X5 ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) ◇ (X0 ◇ (X2 ◇ X3)))) = X6 := superpose eq10 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ (X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) ◇ (X6 ◇ (X2 ◇ X3))) = X0 := superpose eq10 eq11
  have eq72 (X0 X4 X6 : G) : (X4 ◇ X0) = X6 := superpose eq46 eq33
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq72
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq177 eq73


@[equational_result]
theorem Equation13186_implies_Equation2 (G : Type*) [Magma G] (h : Equation13186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation13188_implies_Equation2 (G : Type*) [Magma G] (h : Equation13188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := superpose eq7 eq9
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq19 eq19
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq113 eq43


@[equational_result]
theorem Equation13190_implies_Equation2 (G : Type*) [Magma G] (h : Equation13190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation13192_implies_Equation2 (G : Type*) [Magma G] (h : Equation13192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13193_implies_Equation2 (G : Type*) [Magma G] (h : Equation13193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13194_implies_Equation2 (G : Type*) [Magma G] (h : Equation13194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13196_implies_Equation2 (G : Type*) [Magma G] (h : Equation13196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13197_implies_Equation2 (G : Type*) [Magma G] (h : Equation13197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13198_implies_Equation2 (G : Type*) [Magma G] (h : Equation13198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13200_implies_Equation2 (G : Type*) [Magma G] (h : Equation13200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13201_implies_Equation2 (G : Type*) [Magma G] (h : Equation13201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13202_implies_Equation2 (G : Type*) [Magma G] (h : Equation13202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13203_implies_Equation2 (G : Type*) [Magma G] (h : Equation13203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13205_implies_Equation2 (G : Type*) [Magma G] (h : Equation13205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) = (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := superpose eq7 eq9
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq35
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := superpose eq10 eq35
  have eq72 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := superpose eq10 eq58
  have eq73 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq72 eq56
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq73 eq35
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq7 eq76
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq121 eq77


@[equational_result]
theorem Equation13206_implies_Equation2 (G : Type*) [Magma G] (h : Equation13206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) = (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq7
  have eq32 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose eq11 eq9
  have eq82 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq19 eq10
  have eq108 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq32 eq32
  have eq119 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq32 eq10
  have eq139 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq119 eq108
  have eq140 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq139 eq119
  have eq141 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq139 eq82
  have eq143 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq139 eq140
  have eq144 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq19 eq143
  have eq147 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq19 eq141
  have eq148 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq147 eq144
  have eq150 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq148 eq147
  have eq157 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X1)) = X2 := superpose eq150 eq11
  have eq238 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq150 eq157
  have eq239 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq150 eq238
  have eq240 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq150 eq239
  have eq241 (X0 X1 : G) : X0 = X1 := superpose eq19 eq240
  have eq246 (X0 : G) : sK0 ≠ X0 := superpose eq241 eq8
  subsumption eq246 eq241


@[equational_result]
theorem Equation13207_implies_Equation2 (G : Type*) [Magma G] (h : Equation13207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation13209_implies_Equation2 (G : Type*) [Magma G] (h : Equation13209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13210_implies_Equation2 (G : Type*) [Magma G] (h : Equation13210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13211_implies_Equation2 (G : Type*) [Magma G] (h : Equation13211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13213_implies_Equation2 (G : Type*) [Magma G] (h : Equation13213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13214_implies_Equation2 (G : Type*) [Magma G] (h : Equation13214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13215_implies_Equation2 (G : Type*) [Magma G] (h : Equation13215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13217_implies_Equation2 (G : Type*) [Magma G] (h : Equation13217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13218_implies_Equation2 (G : Type*) [Magma G] (h : Equation13218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13219_implies_Equation2 (G : Type*) [Magma G] (h : Equation13219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13220_implies_Equation2 (G : Type*) [Magma G] (h : Equation13220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13222_implies_Equation2 (G : Type*) [Magma G] (h : Equation13222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation13223_implies_Equation2 (G : Type*) [Magma G] (h : Equation13223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation13224_implies_Equation2 (G : Type*) [Magma G] (h : Equation13224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0))))) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq169 eq48


@[equational_result]
theorem Equation13225_implies_Equation2 (G : Type*) [Magma G] (h : Equation13225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13227_implies_Equation2 (G : Type*) [Magma G] (h : Equation13227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13228_implies_Equation2 (G : Type*) [Magma G] (h : Equation13228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13229_implies_Equation2 (G : Type*) [Magma G] (h : Equation13229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13230_implies_Equation2 (G : Type*) [Magma G] (h : Equation13230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13232_implies_Equation2 (G : Type*) [Magma G] (h : Equation13232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13233_implies_Equation2 (G : Type*) [Magma G] (h : Equation13233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13234_implies_Equation2 (G : Type*) [Magma G] (h : Equation13234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13235_implies_Equation2 (G : Type*) [Magma G] (h : Equation13235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13237_implies_Equation2 (G : Type*) [Magma G] (h : Equation13237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13238_implies_Equation2 (G : Type*) [Magma G] (h : Equation13238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13239_implies_Equation2 (G : Type*) [Magma G] (h : Equation13239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13240_implies_Equation2 (G : Type*) [Magma G] (h : Equation13240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13242_implies_Equation2 (G : Type*) [Magma G] (h : Equation13242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13243_implies_Equation2 (G : Type*) [Magma G] (h : Equation13243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13244_implies_Equation2 (G : Type*) [Magma G] (h : Equation13244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13245_implies_Equation2 (G : Type*) [Magma G] (h : Equation13245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13246_implies_Equation2 (G : Type*) [Magma G] (h : Equation13246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13249_implies_Equation2 (G : Type*) [Magma G] (h : Equation13249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation13250_implies_Equation2 (G : Type*) [Magma G] (h : Equation13250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13253_implies_Equation2 (G : Type*) [Magma G] (h : Equation13253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) = X0 := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) = X2 := superpose eq10 eq7
  have eq55 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0))) = X0 := superpose eq10 eq20
  have eq76 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X2 ◇ X0) ◇ X2) := superpose eq22 eq22
  have eq94 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq76 eq16
  have eq107 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) = X0 := superpose eq94 eq21
  have eq110 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X0 := superpose eq107 eq55
  have eq111 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq110 eq7
  have eq158 (X0 X3 : G) : X0 = X3 := superpose eq111 eq111
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq158 eq8
  subsumption eq160 eq158


@[equational_result]
theorem Equation13254_implies_Equation2 (G : Type*) [Magma G] (h : Equation13254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation13256_implies_Equation2 (G : Type*) [Magma G] (h : Equation13256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X3))) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq49 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1))) = (X3 ◇ X0) := superpose eq11 eq10
  have eq53 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ X0) := superpose eq7 eq49
  have eq57 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq11 eq53
  have eq154 (X0 X3 : G) : X0 = X3 := superpose eq7 eq57
  have eq311 (X0 : G) : sK0 ≠ X0 := superpose eq154 eq8
  subsumption eq311 eq154


@[equational_result]
theorem Equation13257_implies_Equation2 (G : Type*) [Magma G] (h : Equation13257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ (((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13258_implies_Equation2 (G : Type*) [Magma G] (h : Equation13258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13260_implies_Equation2 (G : Type*) [Magma G] (h : Equation13260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation13261_implies_Equation2 (G : Type*) [Magma G] (h : Equation13261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation13262_implies_Equation2 (G : Type*) [Magma G] (h : Equation13262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X4 ◇ (X4 ◇ (X0 ◇ X5))) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13263_implies_Equation2 (G : Type*) [Magma G] (h : Equation13263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13265_implies_Equation2 (G : Type*) [Magma G] (h : Equation13265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := superpose eq7 eq9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0))) = X2 := superpose eq26 eq23
  have eq67 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) ◇ (X1 ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq26
  have eq83 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq67
  have eq140 (X0 X2 : G) : X0 = X2 := superpose eq39 eq83
  have eq263 (X0 : G) : sK0 ≠ X0 := superpose eq140 eq8
  subsumption eq263 eq140


@[equational_result]
theorem Equation13266_implies_Equation2 (G : Type*) [Magma G] (h : Equation13266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X3) = (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq10 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ (X4 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X4)) := superpose eq10 eq9
  have eq36 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X2) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq9
  have eq38 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) ◇ X3) = (X4 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq9 eq9
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq9
  have eq41 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X3))) ◇ X1) = X0 := superpose eq10 eq9
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ X2))) ◇ ((X4 ◇ (X4 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)))) ◇ X4)) = X3 := superpose eq9 eq7
  have eq75 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) = (X3 ◇ (X0 ◇ X2)) := superpose eq9 eq16
  have eq87 (X0 X2 X3 X4 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ X2))) ◇ ((X4 ◇ (X4 ◇ (X0 ◇ X2))) ◇ X4)) = X3 := superpose eq75 eq47
  have eq88 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X2)) = ((X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) ◇ X3) := superpose eq75 eq38
  have eq97 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq88 eq36
  have eq99 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ (X4 ◇ (X2 ◇ X3))) ◇ X4)) := superpose eq97 eq21
  have eq105 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq87 eq99
  have eq106 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq105 eq7
  have eq133 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) ◇ X1) = X0 := superpose eq106 eq41
  have eq134 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq106 eq39
  have eq138 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) = X0 := superpose eq106 eq133
  have eq139 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ X1) = X0 := superpose eq106 eq138
  have eq140 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq106 eq134
  have eq148 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq140 eq139
  have eq153 (X0 X3 : G) : X0 = X3 := superpose eq148 eq148
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq153 eq8
  subsumption eq167 eq153


@[equational_result]
theorem Equation13267_implies_Equation2 (G : Type*) [Magma G] (h : Equation13267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation13269_implies_Equation2 (G : Type*) [Magma G] (h : Equation13269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13270_implies_Equation2 (G : Type*) [Magma G] (h : Equation13270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13271_implies_Equation2 (G : Type*) [Magma G] (h : Equation13271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13273_implies_Equation2 (G : Type*) [Magma G] (h : Equation13273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13274_implies_Equation2 (G : Type*) [Magma G] (h : Equation13274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13275_implies_Equation2 (G : Type*) [Magma G] (h : Equation13275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13277_implies_Equation2 (G : Type*) [Magma G] (h : Equation13277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13278_implies_Equation2 (G : Type*) [Magma G] (h : Equation13278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13279_implies_Equation2 (G : Type*) [Magma G] (h : Equation13279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13280_implies_Equation2 (G : Type*) [Magma G] (h : Equation13280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13283_implies_Equation2 (G : Type*) [Magma G] (h : Equation13283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq69 eq12


@[equational_result]
theorem Equation13284_implies_Equation2 (G : Type*) [Magma G] (h : Equation13284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13286_implies_Equation2 (G : Type*) [Magma G] (h : Equation13286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13287_implies_Equation2 (G : Type*) [Magma G] (h : Equation13287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13288_implies_Equation2 (G : Type*) [Magma G] (h : Equation13288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13290_implies_Equation2 (G : Type*) [Magma G] (h : Equation13290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13291_implies_Equation2 (G : Type*) [Magma G] (h : Equation13291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13292_implies_Equation2 (G : Type*) [Magma G] (h : Equation13292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13294_implies_Equation2 (G : Type*) [Magma G] (h : Equation13294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13295_implies_Equation2 (G : Type*) [Magma G] (h : Equation13295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13296_implies_Equation2 (G : Type*) [Magma G] (h : Equation13296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13297_implies_Equation2 (G : Type*) [Magma G] (h : Equation13297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13299_implies_Equation2 (G : Type*) [Magma G] (h : Equation13299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq55 eq17


@[equational_result]
theorem Equation13300_implies_Equation2 (G : Type*) [Magma G] (h : Equation13300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13301_implies_Equation2 (G : Type*) [Magma G] (h : Equation13301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13302_implies_Equation2 (G : Type*) [Magma G] (h : Equation13302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13304_implies_Equation2 (G : Type*) [Magma G] (h : Equation13304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13305_implies_Equation2 (G : Type*) [Magma G] (h : Equation13305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13306_implies_Equation2 (G : Type*) [Magma G] (h : Equation13306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13307_implies_Equation2 (G : Type*) [Magma G] (h : Equation13307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13309_implies_Equation2 (G : Type*) [Magma G] (h : Equation13309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13310_implies_Equation2 (G : Type*) [Magma G] (h : Equation13310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13311_implies_Equation2 (G : Type*) [Magma G] (h : Equation13311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13312_implies_Equation2 (G : Type*) [Magma G] (h : Equation13312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13314_implies_Equation2 (G : Type*) [Magma G] (h : Equation13314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13315_implies_Equation2 (G : Type*) [Magma G] (h : Equation13315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13316_implies_Equation2 (G : Type*) [Magma G] (h : Equation13316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13317_implies_Equation2 (G : Type*) [Magma G] (h : Equation13317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13319_implies_Equation2 (G : Type*) [Magma G] (h : Equation13319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13320_implies_Equation2 (G : Type*) [Magma G] (h : Equation13320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13321_implies_Equation2 (G : Type*) [Magma G] (h : Equation13321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13322_implies_Equation2 (G : Type*) [Magma G] (h : Equation13322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13323_implies_Equation2 (G : Type*) [Magma G] (h : Equation13323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13325_implies_Equation2 (G : Type*) [Magma G] (h : Equation13325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation13326_implies_Equation2 (G : Type*) [Magma G] (h : Equation13326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation13327_implies_Equation2 (G : Type*) [Magma G] (h : Equation13327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation13328_implies_Equation2 (G : Type*) [Magma G] (h : Equation13328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13330_implies_Equation2 (G : Type*) [Magma G] (h : Equation13330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation13331_implies_Equation2 (G : Type*) [Magma G] (h : Equation13331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation13332_implies_Equation2 (G : Type*) [Magma G] (h : Equation13332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X3 ◇ ((X4 ◇ X1) ◇ (X0 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq56 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq70 (X0 X4 : G) : X0 = X4 := superpose eq7 eq56
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq175 eq70


@[equational_result]
theorem Equation13333_implies_Equation2 (G : Type*) [Magma G] (h : Equation13333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13335_implies_Equation2 (G : Type*) [Magma G] (h : Equation13335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X4) ◇ (X5 ◇ X0)) ◇ X1)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ X3))) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq58 (X0 X1 X2 X3 X7 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X7 := superpose eq10 eq9
  have eq88 (X0 X5 : G) : X0 = X5 := superpose eq58 eq58
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq182 eq88


@[equational_result]
theorem Equation13336_implies_Equation2 (G : Type*) [Magma G] (h : Equation13336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2) ◇ (X4 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13337_implies_Equation2 (G : Type*) [Magma G] (h : Equation13337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq67 eq13


@[equational_result]
theorem Equation13338_implies_Equation2 (G : Type*) [Magma G] (h : Equation13338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13340_implies_Equation2 (G : Type*) [Magma G] (h : Equation13340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation13341_implies_Equation2 (G : Type*) [Magma G] (h : Equation13341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation13342_implies_Equation2 (G : Type*) [Magma G] (h : Equation13342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (((X3 ◇ (X4 ◇ (X0 ◇ X4))) ◇ X4) ◇ X0)) ◇ ((X3 ◇ (X4 ◇ (X0 ◇ X4))) ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13343_implies_Equation2 (G : Type*) [Magma G] (h : Equation13343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13345_implies_Equation2 (G : Type*) [Magma G] (h : Equation13345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation13346_implies_Equation2 (G : Type*) [Magma G] (h : Equation13346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13347_implies_Equation2 (G : Type*) [Magma G] (h : Equation13347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation13348_implies_Equation2 (G : Type*) [Magma G] (h : Equation13348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X5 ◇ (X6 ◇ (X0 ◇ X7))) ◇ X7))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13349_implies_Equation2 (G : Type*) [Magma G] (h : Equation13349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13351_implies_Equation2 (G : Type*) [Magma G] (h : Equation13351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation13352_implies_Equation2 (G : Type*) [Magma G] (h : Equation13352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation13353_implies_Equation2 (G : Type*) [Magma G] (h : Equation13353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X4) ◇ (X2 ◇ X0))))) = X4 := superpose eq7 eq7
  have eq38 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq38
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq170 eq48


@[equational_result]
theorem Equation13354_implies_Equation2 (G : Type*) [Magma G] (h : Equation13354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13356_implies_Equation2 (G : Type*) [Magma G] (h : Equation13356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13357_implies_Equation2 (G : Type*) [Magma G] (h : Equation13357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13358_implies_Equation2 (G : Type*) [Magma G] (h : Equation13358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13359_implies_Equation2 (G : Type*) [Magma G] (h : Equation13359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13361_implies_Equation2 (G : Type*) [Magma G] (h : Equation13361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13362_implies_Equation2 (G : Type*) [Magma G] (h : Equation13362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13363_implies_Equation2 (G : Type*) [Magma G] (h : Equation13363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13364_implies_Equation2 (G : Type*) [Magma G] (h : Equation13364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13366_implies_Equation2 (G : Type*) [Magma G] (h : Equation13366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13367_implies_Equation2 (G : Type*) [Magma G] (h : Equation13367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13368_implies_Equation2 (G : Type*) [Magma G] (h : Equation13368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13369_implies_Equation2 (G : Type*) [Magma G] (h : Equation13369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13371_implies_Equation2 (G : Type*) [Magma G] (h : Equation13371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13372_implies_Equation2 (G : Type*) [Magma G] (h : Equation13372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13373_implies_Equation2 (G : Type*) [Magma G] (h : Equation13373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13374_implies_Equation2 (G : Type*) [Magma G] (h : Equation13374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13375_implies_Equation2 (G : Type*) [Magma G] (h : Equation13375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13377_implies_Equation2 (G : Type*) [Magma G] (h : Equation13377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq23 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq88 eq23


@[equational_result]
theorem Equation13378_implies_Equation2 (G : Type*) [Magma G] (h : Equation13378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13379_implies_Equation2 (G : Type*) [Magma G] (h : Equation13379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13380_implies_Equation2 (G : Type*) [Magma G] (h : Equation13380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13382_implies_Equation2 (G : Type*) [Magma G] (h : Equation13382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13383_implies_Equation2 (G : Type*) [Magma G] (h : Equation13383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13384_implies_Equation2 (G : Type*) [Magma G] (h : Equation13384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13385_implies_Equation2 (G : Type*) [Magma G] (h : Equation13385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13387_implies_Equation2 (G : Type*) [Magma G] (h : Equation13387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13388_implies_Equation2 (G : Type*) [Magma G] (h : Equation13388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13389_implies_Equation2 (G : Type*) [Magma G] (h : Equation13389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13390_implies_Equation2 (G : Type*) [Magma G] (h : Equation13390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13392_implies_Equation2 (G : Type*) [Magma G] (h : Equation13392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13393_implies_Equation2 (G : Type*) [Magma G] (h : Equation13393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13394_implies_Equation2 (G : Type*) [Magma G] (h : Equation13394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13395_implies_Equation2 (G : Type*) [Magma G] (h : Equation13395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13397_implies_Equation2 (G : Type*) [Magma G] (h : Equation13397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13398_implies_Equation2 (G : Type*) [Magma G] (h : Equation13398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13399_implies_Equation2 (G : Type*) [Magma G] (h : Equation13399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13400_implies_Equation2 (G : Type*) [Magma G] (h : Equation13400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13401_implies_Equation2 (G : Type*) [Magma G] (h : Equation13401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13403_implies_Equation2 (G : Type*) [Magma G] (h : Equation13403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation13404_implies_Equation2 (G : Type*) [Magma G] (h : Equation13404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation13405_implies_Equation2 (G : Type*) [Magma G] (h : Equation13405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation13406_implies_Equation2 (G : Type*) [Magma G] (h : Equation13406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13408_implies_Equation2 (G : Type*) [Magma G] (h : Equation13408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13409_implies_Equation2 (G : Type*) [Magma G] (h : Equation13409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13410_implies_Equation2 (G : Type*) [Magma G] (h : Equation13410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13411_implies_Equation2 (G : Type*) [Magma G] (h : Equation13411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13413_implies_Equation2 (G : Type*) [Magma G] (h : Equation13413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13414_implies_Equation2 (G : Type*) [Magma G] (h : Equation13414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13415_implies_Equation2 (G : Type*) [Magma G] (h : Equation13415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13416_implies_Equation2 (G : Type*) [Magma G] (h : Equation13416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13418_implies_Equation2 (G : Type*) [Magma G] (h : Equation13418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13419_implies_Equation2 (G : Type*) [Magma G] (h : Equation13419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13420_implies_Equation2 (G : Type*) [Magma G] (h : Equation13420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13421_implies_Equation2 (G : Type*) [Magma G] (h : Equation13421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13423_implies_Equation2 (G : Type*) [Magma G] (h : Equation13423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13424_implies_Equation2 (G : Type*) [Magma G] (h : Equation13424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13425_implies_Equation2 (G : Type*) [Magma G] (h : Equation13425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13426_implies_Equation2 (G : Type*) [Magma G] (h : Equation13426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13427_implies_Equation2 (G : Type*) [Magma G] (h : Equation13427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13429_implies_Equation2 (G : Type*) [Magma G] (h : Equation13429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation13430_implies_Equation2 (G : Type*) [Magma G] (h : Equation13430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13431_implies_Equation2 (G : Type*) [Magma G] (h : Equation13431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13432_implies_Equation2 (G : Type*) [Magma G] (h : Equation13432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13433_implies_Equation2 (G : Type*) [Magma G] (h : Equation13433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13435_implies_Equation2 (G : Type*) [Magma G] (h : Equation13435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13436_implies_Equation2 (G : Type*) [Magma G] (h : Equation13436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13437_implies_Equation2 (G : Type*) [Magma G] (h : Equation13437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13438_implies_Equation2 (G : Type*) [Magma G] (h : Equation13438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13439_implies_Equation2 (G : Type*) [Magma G] (h : Equation13439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13441_implies_Equation2 (G : Type*) [Magma G] (h : Equation13441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13442_implies_Equation2 (G : Type*) [Magma G] (h : Equation13442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13443_implies_Equation2 (G : Type*) [Magma G] (h : Equation13443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13444_implies_Equation2 (G : Type*) [Magma G] (h : Equation13444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13445_implies_Equation2 (G : Type*) [Magma G] (h : Equation13445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13447_implies_Equation2 (G : Type*) [Magma G] (h : Equation13447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13448_implies_Equation2 (G : Type*) [Magma G] (h : Equation13448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13449_implies_Equation2 (G : Type*) [Magma G] (h : Equation13449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13450_implies_Equation2 (G : Type*) [Magma G] (h : Equation13450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13451_implies_Equation2 (G : Type*) [Magma G] (h : Equation13451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13453_implies_Equation2 (G : Type*) [Magma G] (h : Equation13453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13454_implies_Equation2 (G : Type*) [Magma G] (h : Equation13454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13455_implies_Equation2 (G : Type*) [Magma G] (h : Equation13455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13456_implies_Equation2 (G : Type*) [Magma G] (h : Equation13456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13457_implies_Equation2 (G : Type*) [Magma G] (h : Equation13457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13459_implies_Equation2 (G : Type*) [Magma G] (h : Equation13459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13460_implies_Equation2 (G : Type*) [Magma G] (h : Equation13460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13461_implies_Equation2 (G : Type*) [Magma G] (h : Equation13461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13462_implies_Equation2 (G : Type*) [Magma G] (h : Equation13462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13463_implies_Equation2 (G : Type*) [Magma G] (h : Equation13463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13464_implies_Equation2 (G : Type*) [Magma G] (h : Equation13464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13670_implies_Equation2 (G : Type*) [Magma G] (h : Equation13670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq54 eq13


@[equational_result]
theorem Equation13673_implies_Equation2 (G : Type*) [Magma G] (h : Equation13673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation13675_implies_Equation2 (G : Type*) [Magma G] (h : Equation13675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq97 eq38


@[equational_result]
theorem Equation13676_implies_Equation2 (G : Type*) [Magma G] (h : Equation13676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation13677_implies_Equation2 (G : Type*) [Magma G] (h : Equation13677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq22 eq14


@[equational_result]
theorem Equation13680_implies_Equation2 (G : Type*) [Magma G] (h : Equation13680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq38 eq12


@[equational_result]
theorem Equation13683_implies_Equation2 (G : Type*) [Magma G] (h : Equation13683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation13685_implies_Equation2 (G : Type*) [Magma G] (h : Equation13685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq7
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq11
  have eq29 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1))) = X1 := superpose eq23 eq9
  have eq37 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3))) = X1 := superpose eq23 eq29
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq23 eq37
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq23 eq38
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq39 eq23
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation13686_implies_Equation2 (G : Type*) [Magma G] (h : Equation13686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq11
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X2))) = X1 := superpose eq7 eq11
  have eq36 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq12 eq7
  have eq45 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq36 eq12
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2))) = X1 := superpose eq45 eq13
  have eq59 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq47
  have eq182 (X0 X2 : G) : X0 = X2 := superpose eq59 eq59
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq182 eq8
  subsumption eq187 eq182


@[equational_result]
theorem Equation13687_implies_Equation2 (G : Type*) [Magma G] (h : Equation13687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation13689_implies_Equation2 (G : Type*) [Magma G] (h : Equation13689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq9
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq12
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq21 eq13
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation13690_implies_Equation2 (G : Type*) [Magma G] (h : Equation13690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13691_implies_Equation2 (G : Type*) [Magma G] (h : Equation13691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation13693_implies_Equation2 (G : Type*) [Magma G] (h : Equation13693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq9
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq7 eq17
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq69 eq27


@[equational_result]
theorem Equation13695_implies_Equation2 (G : Type*) [Magma G] (h : Equation13695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation13698_implies_Equation2 (G : Type*) [Magma G] (h : Equation13698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X3))) ◇ ((X0 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13699_implies_Equation2 (G : Type*) [Magma G] (h : Equation13699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation13701_implies_Equation2 (G : Type*) [Magma G] (h : Equation13701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq10
  have eq34 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq30 eq9
  have eq41 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq30 eq34
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq41 eq30
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation13702_implies_Equation2 (G : Type*) [Magma G] (h : Equation13702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ ((X0 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13703_implies_Equation2 (G : Type*) [Magma G] (h : Equation13703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X4) ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation13704_implies_Equation2 (G : Type*) [Magma G] (h : Equation13704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation13707_implies_Equation2 (G : Type*) [Magma G] (h : Equation13707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation13710_implies_Equation2 (G : Type*) [Magma G] (h : Equation13710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation13712_implies_Equation2 (G : Type*) [Magma G] (h : Equation13712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq103 eq40


@[equational_result]
theorem Equation13714_implies_Equation2 (G : Type*) [Magma G] (h : Equation13714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13717_implies_Equation2 (G : Type*) [Magma G] (h : Equation13717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation13720_implies_Equation2 (G : Type*) [Magma G] (h : Equation13720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq36 eq11


@[equational_result]
theorem Equation13722_implies_Equation2 (G : Type*) [Magma G] (h : Equation13722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq47 eq37


@[equational_result]
theorem Equation13723_implies_Equation2 (G : Type*) [Magma G] (h : Equation13723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3)))) = X1 := superpose eq9 eq9
  have eq24 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := superpose eq24 eq7
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq24 eq10
  have eq33 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq24 eq13
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3)))) = X1 := superpose eq24 eq22
  have eq48 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq24 eq33
  have eq49 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq24 eq48
  have eq65 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3)))) = X1 := superpose eq24 eq41
  have eq66 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)))) = X1 := superpose eq24 eq65
  have eq79 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq24 eq28
  have eq89 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq49 eq30
  have eq90 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq30 eq30
  have eq95 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq79 eq89
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq79 eq90
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq95 eq96
  have eq99 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3))) = X1 := superpose eq97 eq66
  have eq118 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) = X1 := superpose eq97 eq99
  have eq119 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq97 eq118
  have eq120 (X0 X1 : G) : X0 = X1 := superpose eq24 eq119
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq128 eq120


@[equational_result]
theorem Equation13724_implies_Equation2 (G : Type*) [Magma G] (h : Equation13724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq25 eq13


@[equational_result]
theorem Equation13726_implies_Equation2 (G : Type*) [Magma G] (h : Equation13726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation13728_implies_Equation2 (G : Type*) [Magma G] (h : Equation13728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation13730_implies_Equation2 (G : Type*) [Magma G] (h : Equation13730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq9
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq15
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation13732_implies_Equation2 (G : Type*) [Magma G] (h : Equation13732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation13734_implies_Equation2 (G : Type*) [Magma G] (h : Equation13734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X1))) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq12 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq65 eq22


@[equational_result]
theorem Equation13736_implies_Equation2 (G : Type*) [Magma G] (h : Equation13736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation13738_implies_Equation2 (G : Type*) [Magma G] (h : Equation13738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq37 eq13


@[equational_result]
theorem Equation13739_implies_Equation2 (G : Type*) [Magma G] (h : Equation13739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13740_implies_Equation2 (G : Type*) [Magma G] (h : Equation13740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ X5)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (((X1 ◇ X3) ◇ X4) ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation13741_implies_Equation2 (G : Type*) [Magma G] (h : Equation13741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13743_implies_Equation2 (G : Type*) [Magma G] (h : Equation13743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)) = X1 := superpose eq10 eq7
  have eq48 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = X2 := superpose eq11 eq7
  have eq51 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X1 := superpose eq48 eq22
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq51
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq140 eq58


@[equational_result]
theorem Equation13744_implies_Equation2 (G : Type*) [Magma G] (h : Equation13744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq56 eq13


@[equational_result]
theorem Equation13745_implies_Equation2 (G : Type*) [Magma G] (h : Equation13745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq58 eq14


@[equational_result]
theorem Equation13747_implies_Equation2 (G : Type*) [Magma G] (h : Equation13747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = (X1 ◇ ((((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) = (X4 ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) ◇ (X1 ◇ X4)) ◇ X4)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) = (((X0 ◇ ((X4 ◇ X0) ◇ X1)) ◇ X1) ◇ ((((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) ◇ X0) ◇ ((X0 ◇ ((X4 ◇ X0) ◇ X1)) ◇ X1))) := superpose eq7 eq9
  have eq31 (X0 X1 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq10
  have eq44 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq31 eq7
  have eq91 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq31 eq44
  have eq97 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)))) = X1 := superpose eq44 eq10
  have eq107 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq31 eq91
  have eq111 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq107 eq31
  have eq112 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq111 eq44
  have eq132 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq112 eq107
  have eq154 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq112 eq132
  have eq193 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq112 eq15
  have eq197 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = (((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ X0)) ◇ X0))) := superpose eq112 eq15
  have eq234 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X4) ◇ ((X4 ◇ ((X5 ◇ X4) ◇ (X6 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))))) ◇ (X6 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))))) = (((X0 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))) ◇ ((((((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X4) ◇ ((X4 ◇ ((X5 ◇ X4) ◇ (X6 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))))) ◇ (X6 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))))) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))))) := superpose eq10 eq13
  have eq282 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) = (X0 ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ X0) ◇ X0)) := superpose eq154 eq13
  have eq285 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) := superpose eq154 eq44
  have eq295 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq154 eq285
  have eq296 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq112 eq295
  have eq297 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq112 eq296
  have eq298 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X0))) ◇ (X4 ◇ X0))) = (X0 ◇ ((((X0 ◇ X2) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X0))) ◇ (X4 ◇ X0))) ◇ X0) ◇ X0)) := superpose eq297 eq282
  have eq306 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X0))) ◇ (X4 ◇ X0))) = X0 := superpose eq297 eq298
  have eq308 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))) ◇ ((((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0))))) := superpose eq306 eq234
  have eq348 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) = (X0 ◇ ((((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq306 eq308
  have eq349 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X3 ◇ X0)) = X0 := superpose eq297 eq348
  have eq351 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq349 eq97
  have eq373 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq351 eq193
  have eq386 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) := superpose eq351 eq373
  have eq387 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) = X1 := superpose eq351 eq386
  have eq388 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X2)) := superpose eq387 eq197
  have eq393 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X2 := superpose eq297 eq388
  have eq394 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq393 eq7
  have eq459 (X0 X2 : G) : X0 = X2 := superpose eq394 eq394
  have eq469 (X0 : G) : sK0 ≠ X0 := superpose eq459 eq8
  subsumption eq469 eq459


@[equational_result]
theorem Equation13749_implies_Equation2 (G : Type*) [Magma G] (h : Equation13749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation13752_implies_Equation2 (G : Type*) [Magma G] (h : Equation13752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation13753_implies_Equation2 (G : Type*) [Magma G] (h : Equation13753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13755_implies_Equation2 (G : Type*) [Magma G] (h : Equation13755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X3) = X0 := superpose eq10 eq11
  have eq55 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq34 eq7
  have eq60 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq55 eq34
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq10 eq60
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq100 eq62


@[equational_result]
theorem Equation13756_implies_Equation2 (G : Type*) [Magma G] (h : Equation13756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13757_implies_Equation2 (G : Type*) [Magma G] (h : Equation13757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X4 ◇ X0) ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation13758_implies_Equation2 (G : Type*) [Magma G] (h : Equation13758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13760_implies_Equation2 (G : Type*) [Magma G] (h : Equation13760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ (X3 ◇ X1)) = (X1 ◇ ((((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ (X3 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) ◇ X0) = X2 := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq16 eq15
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ (X3 ◇ X1)) = (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq16 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X1)) = (X1 ◇ (X3 ◇ X1)) := superpose eq21 eq22
  have eq28 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X0 := superpose eq7 eq23
  have eq52 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq28 eq17
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq88 eq55


@[equational_result]
theorem Equation13762_implies_Equation2 (G : Type*) [Magma G] (h : Equation13762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation13766_implies_Equation2 (G : Type*) [Magma G] (h : Equation13766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation13770_implies_Equation2 (G : Type*) [Magma G] (h : Equation13770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation13772_implies_Equation2 (G : Type*) [Magma G] (h : Equation13772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X2 := superpose eq7 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation13773_implies_Equation2 (G : Type*) [Magma G] (h : Equation13773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13774_implies_Equation2 (G : Type*) [Magma G] (h : Equation13774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation13775_implies_Equation2 (G : Type*) [Magma G] (h : Equation13775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13777_implies_Equation2 (G : Type*) [Magma G] (h : Equation13777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq15 eq7
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation13778_implies_Equation2 (G : Type*) [Magma G] (h : Equation13778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X3 ◇ X3) ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13779_implies_Equation2 (G : Type*) [Magma G] (h : Equation13779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation13783_implies_Equation2 (G : Type*) [Magma G] (h : Equation13783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation13786_implies_Equation2 (G : Type*) [Magma G] (h : Equation13786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X3))) ◇ ((X0 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13787_implies_Equation2 (G : Type*) [Magma G] (h : Equation13787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13789_implies_Equation2 (G : Type*) [Magma G] (h : Equation13789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq48 eq28


@[equational_result]
theorem Equation13790_implies_Equation2 (G : Type*) [Magma G] (h : Equation13790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ ((X0 ◇ ((X3 ◇ X3) ◇ X4)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13791_implies_Equation2 (G : Type*) [Magma G] (h : Equation13791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X4 ◇ X4) ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation13792_implies_Equation2 (G : Type*) [Magma G] (h : Equation13792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13794_implies_Equation2 (G : Type*) [Magma G] (h : Equation13794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation13795_implies_Equation2 (G : Type*) [Magma G] (h : Equation13795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation13796_implies_Equation2 (G : Type*) [Magma G] (h : Equation13796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X4 ◇ X5) ◇ X0)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13797_implies_Equation2 (G : Type*) [Magma G] (h : Equation13797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13799_implies_Equation2 (G : Type*) [Magma G] (h : Equation13799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq31 eq14


@[equational_result]
theorem Equation13800_implies_Equation2 (G : Type*) [Magma G] (h : Equation13800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq43 eq14


@[equational_result]
theorem Equation13801_implies_Equation2 (G : Type*) [Magma G] (h : Equation13801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq48 eq18


@[equational_result]
theorem Equation13802_implies_Equation2 (G : Type*) [Magma G] (h : Equation13802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13804_implies_Equation2 (G : Type*) [Magma G] (h : Equation13804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq14 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X2)) = X0 := superpose eq7 eq10
  have eq23 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq13 eq14
  have eq24 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq23 eq9
  have eq30 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq23 eq24
  have eq39 (X0 X1 : G) : X0 = X1 := superpose eq30 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq49 eq39


@[equational_result]
theorem Equation13805_implies_Equation2 (G : Type*) [Magma G] (h : Equation13805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation13806_implies_Equation2 (G : Type*) [Magma G] (h : Equation13806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X4 ◇ X5) ◇ X4)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13807_implies_Equation2 (G : Type*) [Magma G] (h : Equation13807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13809_implies_Equation2 (G : Type*) [Magma G] (h : Equation13809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq7 eq10
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq159 eq65


@[equational_result]
theorem Equation13810_implies_Equation2 (G : Type*) [Magma G] (h : Equation13810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13811_implies_Equation2 (G : Type*) [Magma G] (h : Equation13811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ ((X4 ◇ X5) ◇ X5)) ◇ X5))) ◇ ((X0 ◇ ((X4 ◇ X5) ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation13812_implies_Equation2 (G : Type*) [Magma G] (h : Equation13812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13814_implies_Equation2 (G : Type*) [Magma G] (h : Equation13814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation13815_implies_Equation2 (G : Type*) [Magma G] (h : Equation13815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13816_implies_Equation2 (G : Type*) [Magma G] (h : Equation13816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X7)) ◇ ((X0 ◇ ((X4 ◇ X5) ◇ X6)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation13817_implies_Equation2 (G : Type*) [Magma G] (h : Equation13817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ ((X5 ◇ X6) ◇ X7)) ◇ X7))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation13818_implies_Equation2 (G : Type*) [Magma G] (h : Equation13818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13821_implies_Equation2 (G : Type*) [Magma G] (h : Equation13821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq37 eq11


@[equational_result]
theorem Equation13824_implies_Equation2 (G : Type*) [Magma G] (h : Equation13824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation13826_implies_Equation2 (G : Type*) [Magma G] (h : Equation13826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq38 eq15


@[equational_result]
theorem Equation13828_implies_Equation2 (G : Type*) [Magma G] (h : Equation13828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation13831_implies_Equation2 (G : Type*) [Magma G] (h : Equation13831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation13834_implies_Equation2 (G : Type*) [Magma G] (h : Equation13834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation13836_implies_Equation2 (G : Type*) [Magma G] (h : Equation13836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation13837_implies_Equation2 (G : Type*) [Magma G] (h : Equation13837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X3 ◇ X1) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ (X3 ◇ X1)) ◇ X4)) ◇ X4))) = X3 := superpose eq7 eq10
  have eq145 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X2)) = X1 := superpose eq7 eq11
  have eq266 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = (((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) ◇ ((((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) ◇ ((X0 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X1 ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4)) := superpose eq9 eq145
  have eq308 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X0 := superpose eq7 eq266
  have eq324 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq308 eq7
  have eq569 (X0 X2 : G) : X0 = X2 := superpose eq324 eq324
  have eq574 (X0 : G) : sK0 ≠ X0 := superpose eq569 eq8
  subsumption eq574 eq569


@[equational_result]
theorem Equation13838_implies_Equation2 (G : Type*) [Magma G] (h : Equation13838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq52 eq12


@[equational_result]
theorem Equation13840_implies_Equation2 (G : Type*) [Magma G] (h : Equation13840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq28 eq13


@[equational_result]
theorem Equation13841_implies_Equation2 (G : Type*) [Magma G] (h : Equation13841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := superpose eq10 eq7
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq10
  have eq35 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq27 eq10
  have eq36 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq27 eq7
  have eq63 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq35 eq10
  have eq96 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X2))) = X0 := superpose eq36 eq9
  have eq106 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq96
  have eq148 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X1 ◇ X0)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq9 eq106
  have eq150 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq27 eq106
  have eq167 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq150 eq63
  have eq169 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq167 eq35
  have eq189 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := superpose eq169 eq14
  have eq192 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq169 eq36
  have eq215 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq27 eq192
  have eq216 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq215 eq148
  have eq219 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq215 eq216
  have eq220 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq215 eq219
  have eq224 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := superpose eq220 eq189
  have eq251 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq220 eq224
  have eq252 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq220 eq251
  have eq253 (X0 X3 : G) : X0 = X3 := superpose eq252 eq252
  have eq272 (X0 : G) : sK0 ≠ X0 := superpose eq253 eq8
  subsumption eq272 eq253


@[equational_result]
theorem Equation13842_implies_Equation2 (G : Type*) [Magma G] (h : Equation13842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation13844_implies_Equation2 (G : Type*) [Magma G] (h : Equation13844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq19 eq16


@[equational_result]
theorem Equation13845_implies_Equation2 (G : Type*) [Magma G] (h : Equation13845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X2)) ◇ X3))) = X2 := superpose eq7 eq9
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X0) := superpose eq7 eq9
  have eq35 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq30 eq7
  have eq46 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X2)) ◇ X3))) = X2 := superpose eq30 eq20
  have eq66 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3))) = X2 := superpose eq30 eq46
  have eq67 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3))) = X2 := superpose eq30 eq66
  have eq86 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq11 eq35
  have eq92 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq30 eq86
  have eq93 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq30 eq92
  have eq97 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq30 eq93
  have eq113 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq93 eq97
  have eq117 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq113 eq67
  have eq144 (X0 X3 : G) : X0 = X3 := superpose eq117 eq117
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq146 eq144


@[equational_result]
theorem Equation13846_implies_Equation2 (G : Type*) [Magma G] (h : Equation13846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation13850_implies_Equation2 (G : Type*) [Magma G] (h : Equation13850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation13852_implies_Equation2 (G : Type*) [Magma G] (h : Equation13852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq41 eq14


@[equational_result]
theorem Equation13853_implies_Equation2 (G : Type*) [Magma G] (h : Equation13853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation13854_implies_Equation2 (G : Type*) [Magma G] (h : Equation13854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13855_implies_Equation2 (G : Type*) [Magma G] (h : Equation13855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation13858_implies_Equation2 (G : Type*) [Magma G] (h : Equation13858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation13861_implies_Equation2 (G : Type*) [Magma G] (h : Equation13861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation13863_implies_Equation2 (G : Type*) [Magma G] (h : Equation13863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq32 eq18


@[equational_result]
theorem Equation13864_implies_Equation2 (G : Type*) [Magma G] (h : Equation13864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := superpose eq11 eq12
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := superpose eq11 eq15
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq16 eq16
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))))) = X2 := superpose eq11 eq16
  have eq46 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq33 eq16
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))))))) = X2 := superpose eq11 eq34
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))))) = X2 := superpose eq11 eq47
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq33 eq48
  have eq69 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq33 eq46
  have eq76 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq69 eq33
  have eq78 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq76 eq49
  have eq86 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq76 eq78
  have eq87 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq113 eq87


@[equational_result]
theorem Equation13865_implies_Equation2 (G : Type*) [Magma G] (h : Equation13865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13868_implies_Equation2 (G : Type*) [Magma G] (h : Equation13868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq66 eq11


@[equational_result]
theorem Equation13870_implies_Equation2 (G : Type*) [Magma G] (h : Equation13870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13871_implies_Equation2 (G : Type*) [Magma G] (h : Equation13871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13873_implies_Equation2 (G : Type*) [Magma G] (h : Equation13873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13874_implies_Equation2 (G : Type*) [Magma G] (h : Equation13874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13875_implies_Equation2 (G : Type*) [Magma G] (h : Equation13875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13877_implies_Equation2 (G : Type*) [Magma G] (h : Equation13877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq32 eq15


@[equational_result]
theorem Equation13879_implies_Equation2 (G : Type*) [Magma G] (h : Equation13879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13881_implies_Equation2 (G : Type*) [Magma G] (h : Equation13881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13882_implies_Equation2 (G : Type*) [Magma G] (h : Equation13882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13883_implies_Equation2 (G : Type*) [Magma G] (h : Equation13883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13885_implies_Equation2 (G : Type*) [Magma G] (h : Equation13885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13886_implies_Equation2 (G : Type*) [Magma G] (h : Equation13886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13887_implies_Equation2 (G : Type*) [Magma G] (h : Equation13887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13889_implies_Equation2 (G : Type*) [Magma G] (h : Equation13889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13890_implies_Equation2 (G : Type*) [Magma G] (h : Equation13890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13891_implies_Equation2 (G : Type*) [Magma G] (h : Equation13891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13892_implies_Equation2 (G : Type*) [Magma G] (h : Equation13892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13894_implies_Equation2 (G : Type*) [Magma G] (h : Equation13894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X2) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X2))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X2 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ X2)) := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) := superpose eq10 eq14
  have eq17 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq16
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = (X2 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq9
  have eq32 (X0 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ X0) := superpose eq17 eq25
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq17
  have eq46 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq37 eq7
  have eq56 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq46 eq32
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq46 eq46
  have eq80 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq78 eq46
  have eq87 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq37 eq80
  have eq88 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq56 eq87
  have eq89 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq56 eq88
  have eq93 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq89 eq80
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq56 eq93
  have eq99 (X0 X2 : G) : X0 = X2 := superpose eq96 eq96
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq104 eq99


@[equational_result]
theorem Equation13896_implies_Equation2 (G : Type*) [Magma G] (h : Equation13896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation13898_implies_Equation2 (G : Type*) [Magma G] (h : Equation13898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose eq11 eq7
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) = X0 := superpose eq11 eq12
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3))) := superpose eq11 eq12
  have eq31 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq12 eq22
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq31 eq21
  have eq42 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := superpose eq31 eq32
  have eq43 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq31 eq42
  have eq71 (X0 X1 : G) : X0 = X1 := superpose eq31 eq43
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq76 eq71


@[equational_result]
theorem Equation13900_implies_Equation2 (G : Type*) [Magma G] (h : Equation13900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation13902_implies_Equation2 (G : Type*) [Magma G] (h : Equation13902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2) = (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X3)) := superpose eq7 eq10
  have eq14 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X1 ◇ X3)) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X1) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) = (X4 ◇ ((X4 ◇ X0) ◇ X4)) := superpose eq7 eq9
  have eq67 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X3) = (X4 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4)) := superpose eq9 eq10
  have eq118 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (X2 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2)) := superpose eq14 eq7
  have eq119 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X4 ◇ ((X1 ◇ X3) ◇ X2)) ◇ X4)) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) := superpose eq14 eq9
  have eq121 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq14 eq10
  have eq168 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) = X2 := superpose eq19 eq7
  have eq198 (X0 X4 : G) : (X4 ◇ ((X4 ◇ X0) ◇ X4)) = X0 := superpose eq168 eq41
  have eq199 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X2) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) := superpose eq198 eq119
  have eq214 (X1 X2 X3 : G) : (X1 ◇ X3) = (X2 ◇ ((X1 ◇ X3) ◇ X2)) := superpose eq199 eq118
  have eq215 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq214 eq121
  have eq221 (X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X2) = ((X2 ◇ (X1 ◇ X3)) ◇ X2) := superpose eq215 eq199
  have eq224 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = X0 := superpose eq221 eq7
  have eq225 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ X3)) := superpose eq221 eq11
  have eq228 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4)) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) := superpose eq221 eq67
  have eq249 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) := superpose eq224 eq228
  have eq250 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq249 eq225
  have eq251 (X0 X1 X3 : G) : ((X1 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X1) = X0 := superpose eq250 eq18
  have eq265 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X1) = X0 := superpose eq250 eq251
  have eq266 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq265 eq224
  have eq276 (X0 X4 : G) : (X4 ◇ (X0 ◇ X4)) = X0 := superpose eq266 eq198
  have eq286 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq266 eq276
  have eq298 (X0 X1 : G) : X0 = X1 := superpose eq266 eq286
  have eq323 (X0 : G) : sK0 ≠ X0 := superpose eq298 eq8
  subsumption eq323 eq298


@[equational_result]
theorem Equation13903_implies_Equation2 (G : Type*) [Magma G] (h : Equation13903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3) = (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) := superpose eq10 eq9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) := superpose eq10 eq12
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq12 eq12
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq10 eq12
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq16 eq18
  have eq24 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq10 eq20
  have eq82 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = ((X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X3) := superpose eq10 eq11
  have eq141 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X3) = X1 := superpose eq12 eq82
  have eq159 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq141 eq141
  have eq175 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq141 eq10
  have eq185 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq159 eq12
  have eq206 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq159 eq14
  have eq215 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)))) := superpose eq159 eq206
  have eq243 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X2 := superpose eq185 eq185
  have eq282 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = X0 := superpose eq24 eq185
  have eq327 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))))) := superpose eq20 eq243
  have eq328 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq24 eq243
  have eq355 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq175 eq327
  have eq356 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose eq24 eq328
  have eq357 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq10 eq356
  have eq358 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq16 eq357
  have eq359 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq215 eq358
  have eq360 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq359 eq24
  have eq365 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq359 eq282
  have eq373 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq360 eq359
  have eq388 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq373 eq365
  have eq389 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq373 eq388
  have eq390 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq389 eq355
  have eq393 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ X1) := superpose eq373 eq390
  have eq394 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq373 eq393
  have eq395 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq394 eq20
  have eq411 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq373 eq395
  have eq567 (X0 X2 : G) : X0 = X2 := superpose eq411 eq411
  have eq572 (X0 : G) : sK0 ≠ X0 := superpose eq567 eq8
  subsumption eq572 eq567


@[equational_result]
theorem Equation13904_implies_Equation2 (G : Type*) [Magma G] (h : Equation13904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation13906_implies_Equation2 (G : Type*) [Magma G] (h : Equation13906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation13907_implies_Equation2 (G : Type*) [Magma G] (h : Equation13907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq65 eq18


@[equational_result]
theorem Equation13908_implies_Equation2 (G : Type*) [Magma G] (h : Equation13908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X4) = X0 := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X1) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4)) = X3 := superpose eq11 eq7
  have eq34 (X1 X3 X5 : G) : ((X5 ◇ X1) ◇ X3) = X3 := superpose eq21 eq27
  have eq35 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X3) ◇ X3)) = X0 := superpose eq34 eq7
  have eq52 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq34 eq35
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq55 eq53


@[equational_result]
theorem Equation13909_implies_Equation2 (G : Type*) [Magma G] (h : Equation13909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13911_implies_Equation2 (G : Type*) [Magma G] (h : Equation13911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) ◇ ((((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X2 ◇ X1)) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1)) = (X1 ◇ ((X1 ◇ X3) ◇ X1)) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X1))) = X3 := superpose eq11 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X2 ◇ X0)) ◇ X1) = ((((X2 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq10 eq20
  have eq38 (X0 X1 X4 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X4)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = (((X1 ◇ X0) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X4) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq20 eq10
  have eq43 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X2 ◇ X0)) ◇ X1) = ((((X2 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq17 eq34
  have eq44 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ (X2 ◇ X0)) ◇ X1) = ((X0 ◇ ((X0 ◇ X4) ◇ X0)) ◇ X1) := superpose eq10 eq43
  have eq310 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) = X0 := superpose eq44 eq7
  have eq311 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = ((X3 ◇ X2) ◇ (X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) := superpose eq44 eq17
  have eq378 (X0 X2 X3 X4 : G) : (X4 ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq310 eq311
  have eq398 (X0 X1 X4 X5 : G) : ((X4 ◇ X5) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq20 eq378
  have eq516 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X4) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq398 eq38
  have eq863 (X0 X2 : G) : X0 = X2 := superpose eq7 eq516
  have eq913 (X0 : G) : sK0 ≠ X0 := superpose eq863 eq8
  subsumption eq913 eq863


@[equational_result]
theorem Equation13913_implies_Equation2 (G : Type*) [Magma G] (h : Equation13913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq76 eq12


@[equational_result]
theorem Equation13915_implies_Equation2 (G : Type*) [Magma G] (h : Equation13915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13916_implies_Equation2 (G : Type*) [Magma G] (h : Equation13916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13917_implies_Equation2 (G : Type*) [Magma G] (h : Equation13917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13919_implies_Equation2 (G : Type*) [Magma G] (h : Equation13919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13920_implies_Equation2 (G : Type*) [Magma G] (h : Equation13920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13921_implies_Equation2 (G : Type*) [Magma G] (h : Equation13921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13923_implies_Equation2 (G : Type*) [Magma G] (h : Equation13923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13924_implies_Equation2 (G : Type*) [Magma G] (h : Equation13924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13925_implies_Equation2 (G : Type*) [Magma G] (h : Equation13925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13926_implies_Equation2 (G : Type*) [Magma G] (h : Equation13926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13930_implies_Equation2 (G : Type*) [Magma G] (h : Equation13930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation13932_implies_Equation2 (G : Type*) [Magma G] (h : Equation13932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13933_implies_Equation2 (G : Type*) [Magma G] (h : Equation13933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13934_implies_Equation2 (G : Type*) [Magma G] (h : Equation13934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13936_implies_Equation2 (G : Type*) [Magma G] (h : Equation13936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13937_implies_Equation2 (G : Type*) [Magma G] (h : Equation13937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation13938_implies_Equation2 (G : Type*) [Magma G] (h : Equation13938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13940_implies_Equation2 (G : Type*) [Magma G] (h : Equation13940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13941_implies_Equation2 (G : Type*) [Magma G] (h : Equation13941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13942_implies_Equation2 (G : Type*) [Magma G] (h : Equation13942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13943_implies_Equation2 (G : Type*) [Magma G] (h : Equation13943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13945_implies_Equation2 (G : Type*) [Magma G] (h : Equation13945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq31 eq14


@[equational_result]
theorem Equation13946_implies_Equation2 (G : Type*) [Magma G] (h : Equation13946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation13947_implies_Equation2 (G : Type*) [Magma G] (h : Equation13947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq11
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq168 eq47


@[equational_result]
theorem Equation13948_implies_Equation2 (G : Type*) [Magma G] (h : Equation13948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation13950_implies_Equation2 (G : Type*) [Magma G] (h : Equation13950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13951_implies_Equation2 (G : Type*) [Magma G] (h : Equation13951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13952_implies_Equation2 (G : Type*) [Magma G] (h : Equation13952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13953_implies_Equation2 (G : Type*) [Magma G] (h : Equation13953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13955_implies_Equation2 (G : Type*) [Magma G] (h : Equation13955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13956_implies_Equation2 (G : Type*) [Magma G] (h : Equation13956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13957_implies_Equation2 (G : Type*) [Magma G] (h : Equation13957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13958_implies_Equation2 (G : Type*) [Magma G] (h : Equation13958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13960_implies_Equation2 (G : Type*) [Magma G] (h : Equation13960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation13961_implies_Equation2 (G : Type*) [Magma G] (h : Equation13961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13962_implies_Equation2 (G : Type*) [Magma G] (h : Equation13962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation13963_implies_Equation2 (G : Type*) [Magma G] (h : Equation13963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13965_implies_Equation2 (G : Type*) [Magma G] (h : Equation13965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13966_implies_Equation2 (G : Type*) [Magma G] (h : Equation13966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13967_implies_Equation2 (G : Type*) [Magma G] (h : Equation13967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13968_implies_Equation2 (G : Type*) [Magma G] (h : Equation13968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation13969_implies_Equation2 (G : Type*) [Magma G] (h : Equation13969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation13971_implies_Equation2 (G : Type*) [Magma G] (h : Equation13971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq33 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq10 eq7
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq108 eq41


@[equational_result]
theorem Equation13972_implies_Equation2 (G : Type*) [Magma G] (h : Equation13972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq56 eq14


@[equational_result]
theorem Equation13973_implies_Equation2 (G : Type*) [Magma G] (h : Equation13973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq56 eq14


@[equational_result]
theorem Equation13975_implies_Equation2 (G : Type*) [Magma G] (h : Equation13975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = X1 := superpose eq10 eq7
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) = X0 := superpose eq10 eq9
  have eq28 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq9
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq14
  have eq45 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq10 eq14
  have eq50 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq43
  have eq51 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq50 eq28
  have eq52 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq10 eq51
  have eq53 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq50 eq52
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq53 eq7
  have eq57 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq53 eq7
  have eq68 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq56 eq27
  have eq69 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq50 eq68
  have eq70 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq57 eq69
  have eq76 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq70 eq7
  have eq105 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq76 eq45
  have eq107 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose eq105 eq14
  have eq113 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq105 eq107
  have eq158 (X0 X2 : G) : X0 = X2 := superpose eq113 eq113
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq158 eq8
  subsumption eq163 eq158


@[equational_result]
theorem Equation13977_implies_Equation2 (G : Type*) [Magma G] (h : Equation13977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation13980_implies_Equation2 (G : Type*) [Magma G] (h : Equation13980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation13981_implies_Equation2 (G : Type*) [Magma G] (h : Equation13981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq67 eq12


@[equational_result]
theorem Equation13983_implies_Equation2 (G : Type*) [Magma G] (h : Equation13983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation13984_implies_Equation2 (G : Type*) [Magma G] (h : Equation13984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13985_implies_Equation2 (G : Type*) [Magma G] (h : Equation13985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X4 ◇ ((X0 ◇ X0) ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation13986_implies_Equation2 (G : Type*) [Magma G] (h : Equation13986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation13988_implies_Equation2 (G : Type*) [Magma G] (h : Equation13988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq11 eq13
  have eq33 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq10 eq15
  have eq35 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq15 eq15
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)) := superpose eq15 eq7
  have eq46 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq33
  have eq48 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq10 eq35
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)) := superpose eq48 eq42
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) := superpose eq11 eq11
  have eq60 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0) := superpose eq15 eq11
  have eq112 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0) := superpose eq48 eq60
  have eq113 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0) = X1 := superpose eq10 eq112
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq113 eq51
  have eq116 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq114 eq55
  have eq122 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) := superpose eq114 eq116
  have eq123 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq122 eq7
  have eq134 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose eq123 eq10
  have eq136 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq123 eq46
  have eq143 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq123 eq114
  have eq150 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq143 eq134
  have eq151 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq143 eq136
  have eq152 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq123 eq151
  have eq160 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq152 eq150
  have eq167 (X0 X2 : G) : X0 = X2 := superpose eq160 eq160
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq169 eq167


@[equational_result]
theorem Equation13989_implies_Equation2 (G : Type*) [Magma G] (h : Equation13989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation13990_implies_Equation2 (G : Type*) [Magma G] (h : Equation13990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation13993_implies_Equation2 (G : Type*) [Magma G] (h : Equation13993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1))) ◇ X3)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq10
  have eq13 (X0 X1 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose eq10 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq12
  have eq17 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := superpose eq16 eq13
  have eq44 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq17 eq7
  have eq77 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq17 eq44
  have eq97 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq77 eq17
  have eq105 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ ((X3 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1)) ◇ X3)) = X2 := superpose eq97 eq9
  have eq141 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X3) = X2 := superpose eq97 eq105
  have eq142 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq97 eq141
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq142 eq142
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq145 eq143


@[equational_result]
theorem Equation13994_implies_Equation2 (G : Type*) [Magma G] (h : Equation13994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation13996_implies_Equation2 (G : Type*) [Magma G] (h : Equation13996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq7
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq125 eq42


@[equational_result]
theorem Equation13997_implies_Equation2 (G : Type*) [Magma G] (h : Equation13997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X2)) ◇ X2) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) = X2 := superpose eq13 eq9
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ (X3 ◇ X1)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X2))) = X3 := superpose eq13 eq10
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) = X2 := superpose eq13 eq17
  have eq21 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq20 eq19
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq11 eq21
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq65 eq27


@[equational_result]
theorem Equation13998_implies_Equation2 (G : Type*) [Magma G] (h : Equation13998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation14000_implies_Equation2 (G : Type*) [Magma G] (h : Equation14000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation14001_implies_Equation2 (G : Type*) [Magma G] (h : Equation14001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation14002_implies_Equation2 (G : Type*) [Magma G] (h : Equation14002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq65 eq21


@[equational_result]
theorem Equation14003_implies_Equation2 (G : Type*) [Magma G] (h : Equation14003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14006_implies_Equation2 (G : Type*) [Magma G] (h : Equation14006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14007_implies_Equation2 (G : Type*) [Magma G] (h : Equation14007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14011_implies_Equation2 (G : Type*) [Magma G] (h : Equation14011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation14013_implies_Equation2 (G : Type*) [Magma G] (h : Equation14013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation14014_implies_Equation2 (G : Type*) [Magma G] (h : Equation14014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2))) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation14015_implies_Equation2 (G : Type*) [Magma G] (h : Equation14015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation14017_implies_Equation2 (G : Type*) [Magma G] (h : Equation14017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation14018_implies_Equation2 (G : Type*) [Magma G] (h : Equation14018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14019_implies_Equation2 (G : Type*) [Magma G] (h : Equation14019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation14020_implies_Equation2 (G : Type*) [Magma G] (h : Equation14020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14022_implies_Equation2 (G : Type*) [Magma G] (h : Equation14022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation14023_implies_Equation2 (G : Type*) [Magma G] (h : Equation14023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14024_implies_Equation2 (G : Type*) [Magma G] (h : Equation14024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ X5) ◇ X0)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14025_implies_Equation2 (G : Type*) [Magma G] (h : Equation14025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14027_implies_Equation2 (G : Type*) [Magma G] (h : Equation14027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation14028_implies_Equation2 (G : Type*) [Magma G] (h : Equation14028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq11 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14029_implies_Equation2 (G : Type*) [Magma G] (h : Equation14029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq63 eq21


@[equational_result]
theorem Equation14030_implies_Equation2 (G : Type*) [Magma G] (h : Equation14030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14032_implies_Equation2 (G : Type*) [Magma G] (h : Equation14032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation14033_implies_Equation2 (G : Type*) [Magma G] (h : Equation14033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation14034_implies_Equation2 (G : Type*) [Magma G] (h : Equation14034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X4 ◇ ((X0 ◇ X5) ◇ X4)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14035_implies_Equation2 (G : Type*) [Magma G] (h : Equation14035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14037_implies_Equation2 (G : Type*) [Magma G] (h : Equation14037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq58 eq15


@[equational_result]
theorem Equation14038_implies_Equation2 (G : Type*) [Magma G] (h : Equation14038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation14039_implies_Equation2 (G : Type*) [Magma G] (h : Equation14039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X4 ◇ ((X0 ◇ X5) ◇ X5)) ◇ X5))) ◇ ((X4 ◇ ((X0 ◇ X5) ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation14040_implies_Equation2 (G : Type*) [Magma G] (h : Equation14040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation14042_implies_Equation2 (G : Type*) [Magma G] (h : Equation14042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation14043_implies_Equation2 (G : Type*) [Magma G] (h : Equation14043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14044_implies_Equation2 (G : Type*) [Magma G] (h : Equation14044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X7)) ◇ ((X4 ◇ ((X0 ◇ X5) ◇ X6)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14045_implies_Equation2 (G : Type*) [Magma G] (h : Equation14045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X5 ◇ ((X0 ◇ X6) ◇ X7)) ◇ X7))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation14046_implies_Equation2 (G : Type*) [Magma G] (h : Equation14046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14048_implies_Equation2 (G : Type*) [Magma G] (h : Equation14048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq12 eq12
  have eq15 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq12 eq12
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq12 eq7
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0)) = X1 := superpose eq12 eq7
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ X2)) = X1 := superpose eq12 eq7
  have eq28 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X1 ◇ ((X2 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X3 ◇ X1) ◇ X1))) ◇ X1)) := superpose eq12 eq7
  have eq33 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq19 eq19
  have eq39 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq19 eq33
  have eq119 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) = (((X2 ◇ X1) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq12 eq15
  have eq120 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq19 eq15
  have eq143 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq15 eq12
  have eq167 (X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq26 eq119
  have eq168 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq167 eq14
  have eq172 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq167 eq23
  have eq174 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq168 eq12
  have eq181 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq168 eq39
  have eq202 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ ((X3 ◇ X1) ◇ X1))) ◇ X1)) := superpose eq174 eq28
  have eq219 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq168 eq120
  have eq220 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq168 eq219
  have eq221 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq172 eq220
  have eq255 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq168 eq143
  have eq256 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq168 eq255
  have eq259 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq256 eq181
  have eq263 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq221 eq259
  have eq264 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq263 eq168
  have eq269 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X1 ◇ ((X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) ◇ X1)) := superpose eq263 eq202
  have eq280 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X1) = (X1 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq264 eq269
  have eq281 (X1 X3 : G) : ((X3 ◇ X1) ◇ X1) = X1 := superpose eq264 eq280
  have eq282 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq281 eq7
  have eq454 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq282 eq282
  have eq456 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq172 eq454
  have eq464 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq456 eq282
  have eq477 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq464 eq456
  have eq481 (X0 X1 : G) : X0 = X1 := superpose eq464 eq477
  have eq483 (X0 : G) : sK0 ≠ X0 := superpose eq481 eq8
  subsumption eq483 eq481


@[equational_result]
theorem Equation14050_implies_Equation2 (G : Type*) [Magma G] (h : Equation14050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation14052_implies_Equation2 (G : Type*) [Magma G] (h : Equation14052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) := superpose eq10 eq12
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq12 eq12
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq10 eq12
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq10 eq18
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X2 ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0)) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) = X1 := superpose eq20 eq12
  have eq47 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) ◇ (X3 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))))))) = (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) ◇ X0) := superpose eq20 eq16
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := superpose eq12 eq16
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := superpose eq10 eq49
  have eq71 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) ◇ X0) = (X1 ◇ (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) ◇ X0)) := superpose eq69 eq47
  have eq72 (X0 X1 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) = X1 := superpose eq69 eq25
  have eq75 (X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X2 ◇ X3)) := superpose eq72 eq71
  have eq78 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ X1) := superpose eq75 eq10
  have eq80 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq75 eq12
  have eq82 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq75 eq14
  have eq113 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq75 eq80
  have eq116 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq75 eq82
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq78 eq116
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq113 eq117
  have eq121 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq118 eq113
  have eq125 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq118 eq121
  have eq185 (X0 X2 : G) : X0 = X2 := superpose eq125 eq125
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq185 eq8
  subsumption eq187 eq185


@[equational_result]
theorem Equation14053_implies_Equation2 (G : Type*) [Magma G] (h : Equation14053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) = X0 := superpose eq7 eq10
  have eq30 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq17
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := superpose eq30 eq7
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = X0 := superpose eq30 eq19
  have eq36 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq30 eq35
  have eq37 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq36 eq34
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq37 eq36
  have eq56 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq37 eq48
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq56 eq56
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq62 eq57


@[equational_result]
theorem Equation14054_implies_Equation2 (G : Type*) [Magma G] (h : Equation14054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation14056_implies_Equation2 (G : Type*) [Magma G] (h : Equation14056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (((X1 ◇ X3) ◇ X0) ◇ X2)) ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation14058_implies_Equation2 (G : Type*) [Magma G] (h : Equation14058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14060_implies_Equation2 (G : Type*) [Magma G] (h : Equation14060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq65 eq18


@[equational_result]
theorem Equation14061_implies_Equation2 (G : Type*) [Magma G] (h : Equation14061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq66 eq17


@[equational_result]
theorem Equation14062_implies_Equation2 (G : Type*) [Magma G] (h : Equation14062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X4) = X0 := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4)) = X3 := superpose eq11 eq7
  have eq34 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq21 eq27
  have eq35 (X0 X1 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ X3)) = X0 := superpose eq34 eq7
  have eq53 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq34 eq35
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq56 eq54


@[equational_result]
theorem Equation14063_implies_Equation2 (G : Type*) [Magma G] (h : Equation14063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14065_implies_Equation2 (G : Type*) [Magma G] (h : Equation14065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq10
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq10 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose eq16 eq12
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq16 eq9
  have eq33 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X2)) = (((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq19 eq19
  have eq41 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ X1)) = (X1 ◇ ((X3 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X1)) := superpose eq19 eq7
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ X1)) = (X1 ◇ ((X3 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)) := superpose eq16 eq41
  have eq51 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq16 eq16
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq16 eq19
  have eq68 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X2)) = (((X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq51 eq33
  have eq75 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq16 eq58
  have eq76 (X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ X1)) = (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X1)) := superpose eq75 eq50
  have eq78 (X1 X2 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := superpose eq7 eq76
  have eq84 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1)) ◇ X0)) = X1 := superpose eq78 eq18
  have eq85 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X2)) = ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq78 eq68
  have eq88 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X2 ◇ ((X3 ◇ X1) ◇ X2)) := superpose eq7 eq85
  have eq89 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose eq88 eq84
  have eq115 (X0 X1 : G) : X0 = X1 := superpose eq10 eq89
  have eq225 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq225 eq115


@[equational_result]
theorem Equation14067_implies_Equation2 (G : Type*) [Magma G] (h : Equation14067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation14069_implies_Equation2 (G : Type*) [Magma G] (h : Equation14069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation14070_implies_Equation2 (G : Type*) [Magma G] (h : Equation14070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14071_implies_Equation2 (G : Type*) [Magma G] (h : Equation14071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14073_implies_Equation2 (G : Type*) [Magma G] (h : Equation14073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14074_implies_Equation2 (G : Type*) [Magma G] (h : Equation14074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14075_implies_Equation2 (G : Type*) [Magma G] (h : Equation14075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14077_implies_Equation2 (G : Type*) [Magma G] (h : Equation14077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14078_implies_Equation2 (G : Type*) [Magma G] (h : Equation14078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14079_implies_Equation2 (G : Type*) [Magma G] (h : Equation14079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14080_implies_Equation2 (G : Type*) [Magma G] (h : Equation14080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14084_implies_Equation2 (G : Type*) [Magma G] (h : Equation14084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation14086_implies_Equation2 (G : Type*) [Magma G] (h : Equation14086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14087_implies_Equation2 (G : Type*) [Magma G] (h : Equation14087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14088_implies_Equation2 (G : Type*) [Magma G] (h : Equation14088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14090_implies_Equation2 (G : Type*) [Magma G] (h : Equation14090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14091_implies_Equation2 (G : Type*) [Magma G] (h : Equation14091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14092_implies_Equation2 (G : Type*) [Magma G] (h : Equation14092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14094_implies_Equation2 (G : Type*) [Magma G] (h : Equation14094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14095_implies_Equation2 (G : Type*) [Magma G] (h : Equation14095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14096_implies_Equation2 (G : Type*) [Magma G] (h : Equation14096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14097_implies_Equation2 (G : Type*) [Magma G] (h : Equation14097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14099_implies_Equation2 (G : Type*) [Magma G] (h : Equation14099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation14100_implies_Equation2 (G : Type*) [Magma G] (h : Equation14100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (((X1 ◇ X3) ◇ X5) ◇ X0)) ◇ X4) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ (((X1 ◇ X3) ◇ X5) ◇ X0)) ◇ X4) = X1 := superpose eq11 eq10
  have eq15 (X1 X4 : G) : (X4 ◇ X4) = X1 := superpose eq11 eq13
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation14101_implies_Equation2 (G : Type*) [Magma G] (h : Equation14101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq11
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq171 eq46


@[equational_result]
theorem Equation14102_implies_Equation2 (G : Type*) [Magma G] (h : Equation14102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14104_implies_Equation2 (G : Type*) [Magma G] (h : Equation14104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14105_implies_Equation2 (G : Type*) [Magma G] (h : Equation14105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14106_implies_Equation2 (G : Type*) [Magma G] (h : Equation14106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14107_implies_Equation2 (G : Type*) [Magma G] (h : Equation14107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14109_implies_Equation2 (G : Type*) [Magma G] (h : Equation14109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14110_implies_Equation2 (G : Type*) [Magma G] (h : Equation14110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14111_implies_Equation2 (G : Type*) [Magma G] (h : Equation14111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14112_implies_Equation2 (G : Type*) [Magma G] (h : Equation14112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14114_implies_Equation2 (G : Type*) [Magma G] (h : Equation14114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14115_implies_Equation2 (G : Type*) [Magma G] (h : Equation14115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14116_implies_Equation2 (G : Type*) [Magma G] (h : Equation14116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14117_implies_Equation2 (G : Type*) [Magma G] (h : Equation14117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14119_implies_Equation2 (G : Type*) [Magma G] (h : Equation14119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14120_implies_Equation2 (G : Type*) [Magma G] (h : Equation14120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14121_implies_Equation2 (G : Type*) [Magma G] (h : Equation14121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14122_implies_Equation2 (G : Type*) [Magma G] (h : Equation14122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14123_implies_Equation2 (G : Type*) [Magma G] (h : Equation14123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14126_implies_Equation2 (G : Type*) [Magma G] (h : Equation14126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation14127_implies_Equation2 (G : Type*) [Magma G] (h : Equation14127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq57 eq14


@[equational_result]
theorem Equation14129_implies_Equation2 (G : Type*) [Magma G] (h : Equation14129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X2) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) ◇ X1)) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = X1 := superpose eq11 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq11 eq14
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq11 eq17
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X5)) = (((X3 ◇ ((X3 ◇ X2) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X4)) ◇ X4) := superpose eq9 eq9
  have eq42 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X4)) ◇ X4) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq9 eq9
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X2) = X0 := superpose eq7 eq9
  have eq58 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X2 := superpose eq43 eq42
  have eq66 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq11 eq18
  have eq135 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq9 eq43
  have eq142 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq43 eq7
  have eq152 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq43 eq18
  have eq161 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X2) = X0 := superpose eq142 eq43
  have eq171 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) := superpose eq142 eq152
  have eq180 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq58
  have eq297 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) := superpose eq66 eq12
  have eq301 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) := superpose eq66 eq10
  have eq303 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X1 := superpose eq66 eq161
  have eq315 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X1 := superpose eq11 eq303
  have eq316 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X1 := superpose eq180 eq315
  have eq317 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X1 := superpose eq58 eq316
  have eq319 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq317 eq301
  have eq321 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) = X1 := superpose eq319 eq317
  have eq322 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := superpose eq171 eq321
  have eq434 (X0 X1 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq135 eq135
  have eq466 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq135 eq434
  have eq476 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq466 eq297
  have eq479 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X1 := superpose eq466 eq322
  have eq517 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq466 eq476
  have eq518 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq466 eq517
  have eq519 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) := superpose eq466 eq518
  have eq527 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq466 eq479
  have eq528 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq466 eq527
  have eq529 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq466 eq528
  have eq530 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ X1)) := superpose eq529 eq519
  have eq534 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq466 eq530
  have eq535 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq466 eq534
  have eq536 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X5)) = (((X3 ◇ ((X3 ◇ X2) ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X4)) ◇ X4) := superpose eq535 eq24
  have eq756 (X1 X4 X5 : G) : (X5 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X5)) = X4 := superpose eq535 eq536
  have eq757 (X4 X5 : G) : (X5 ◇ X5) = X4 := superpose eq535 eq756
  have eq765 (X0 X2 : G) : X0 = X2 := superpose eq757 eq757
  have eq767 (X0 : G) : sK0 ≠ X0 := superpose eq765 eq8
  subsumption eq767 eq765


@[equational_result]
theorem Equation14131_implies_Equation2 (G : Type*) [Magma G] (h : Equation14131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation14133_implies_Equation2 (G : Type*) [Magma G] (h : Equation14133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2) = (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X3 ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X3)) := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = X1 := superpose eq10 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X3 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ X4) = (X5 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X5)) := superpose eq9 eq9
  have eq76 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ ((X3 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ X4) := superpose eq12 eq46
  have eq77 (X1 X2 X4 : G) : (X1 ◇ X2) = (X1 ◇ X4) := superpose eq21 eq76
  have eq82 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq7 eq77
  have eq177 (X0 X3 : G) : X0 = X3 := superpose eq7 eq82
  have eq323 (X0 : G) : sK0 ≠ X0 := superpose eq177 eq8
  subsumption eq323 eq177


@[equational_result]
theorem Equation14134_implies_Equation2 (G : Type*) [Magma G] (h : Equation14134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq76 eq14


@[equational_result]
theorem Equation14135_implies_Equation2 (G : Type*) [Magma G] (h : Equation14135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq57 eq13


@[equational_result]
theorem Equation14137_implies_Equation2 (G : Type*) [Magma G] (h : Equation14137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation14138_implies_Equation2 (G : Type*) [Magma G] (h : Equation14138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14139_implies_Equation2 (G : Type*) [Magma G] (h : Equation14139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ X5)) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation14140_implies_Equation2 (G : Type*) [Magma G] (h : Equation14140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation14144_implies_Equation2 (G : Type*) [Magma G] (h : Equation14144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq54 eq13


@[equational_result]
theorem Equation14146_implies_Equation2 (G : Type*) [Magma G] (h : Equation14146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14147_implies_Equation2 (G : Type*) [Magma G] (h : Equation14147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14148_implies_Equation2 (G : Type*) [Magma G] (h : Equation14148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14150_implies_Equation2 (G : Type*) [Magma G] (h : Equation14150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14151_implies_Equation2 (G : Type*) [Magma G] (h : Equation14151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14152_implies_Equation2 (G : Type*) [Magma G] (h : Equation14152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14154_implies_Equation2 (G : Type*) [Magma G] (h : Equation14154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14155_implies_Equation2 (G : Type*) [Magma G] (h : Equation14155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14156_implies_Equation2 (G : Type*) [Magma G] (h : Equation14156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14157_implies_Equation2 (G : Type*) [Magma G] (h : Equation14157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14160_implies_Equation2 (G : Type*) [Magma G] (h : Equation14160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation14161_implies_Equation2 (G : Type*) [Magma G] (h : Equation14161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq69 eq12


@[equational_result]
theorem Equation14163_implies_Equation2 (G : Type*) [Magma G] (h : Equation14163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14164_implies_Equation2 (G : Type*) [Magma G] (h : Equation14164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14165_implies_Equation2 (G : Type*) [Magma G] (h : Equation14165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14167_implies_Equation2 (G : Type*) [Magma G] (h : Equation14167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation14168_implies_Equation2 (G : Type*) [Magma G] (h : Equation14168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14169_implies_Equation2 (G : Type*) [Magma G] (h : Equation14169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14171_implies_Equation2 (G : Type*) [Magma G] (h : Equation14171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14172_implies_Equation2 (G : Type*) [Magma G] (h : Equation14172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14173_implies_Equation2 (G : Type*) [Magma G] (h : Equation14173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14174_implies_Equation2 (G : Type*) [Magma G] (h : Equation14174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14176_implies_Equation2 (G : Type*) [Magma G] (h : Equation14176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation14177_implies_Equation2 (G : Type*) [Magma G] (h : Equation14177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation14178_implies_Equation2 (G : Type*) [Magma G] (h : Equation14178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ ((X3 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation14179_implies_Equation2 (G : Type*) [Magma G] (h : Equation14179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation14181_implies_Equation2 (G : Type*) [Magma G] (h : Equation14181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14182_implies_Equation2 (G : Type*) [Magma G] (h : Equation14182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14183_implies_Equation2 (G : Type*) [Magma G] (h : Equation14183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14184_implies_Equation2 (G : Type*) [Magma G] (h : Equation14184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14186_implies_Equation2 (G : Type*) [Magma G] (h : Equation14186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14187_implies_Equation2 (G : Type*) [Magma G] (h : Equation14187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14188_implies_Equation2 (G : Type*) [Magma G] (h : Equation14188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14189_implies_Equation2 (G : Type*) [Magma G] (h : Equation14189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14191_implies_Equation2 (G : Type*) [Magma G] (h : Equation14191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation14192_implies_Equation2 (G : Type*) [Magma G] (h : Equation14192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14193_implies_Equation2 (G : Type*) [Magma G] (h : Equation14193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation14194_implies_Equation2 (G : Type*) [Magma G] (h : Equation14194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14196_implies_Equation2 (G : Type*) [Magma G] (h : Equation14196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14197_implies_Equation2 (G : Type*) [Magma G] (h : Equation14197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14198_implies_Equation2 (G : Type*) [Magma G] (h : Equation14198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14199_implies_Equation2 (G : Type*) [Magma G] (h : Equation14199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14200_implies_Equation2 (G : Type*) [Magma G] (h : Equation14200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation14202_implies_Equation2 (G : Type*) [Magma G] (h : Equation14202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))) ◇ X0) = X5 := superpose eq7 eq7
  have eq59 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X1)) = X5 := superpose eq11 eq7
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq59
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq157 eq67


@[equational_result]
theorem Equation14203_implies_Equation2 (G : Type*) [Magma G] (h : Equation14203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation14204_implies_Equation2 (G : Type*) [Magma G] (h : Equation14204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq70 eq13


@[equational_result]
theorem Equation14205_implies_Equation2 (G : Type*) [Magma G] (h : Equation14205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation14207_implies_Equation2 (G : Type*) [Magma G] (h : Equation14207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2)) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X2)) = X1 := superpose eq11 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2))) = X1 := superpose eq11 eq23
  have eq29 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq7 eq28
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) = X0 := superpose eq29 eq22
  have eq45 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq29 eq30
  have eq71 (X0 X1 : G) : X0 = X1 := superpose eq29 eq45
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq76 eq71


@[equational_result]
theorem Equation14208_implies_Equation2 (G : Type*) [Magma G] (h : Equation14208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3))) = X0 := superpose eq7 eq11
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = X1 := superpose eq11 eq7
  have eq34 (X0 X1 X5 : G) : (X5 ◇ X1) = X0 := superpose eq24 eq16
  have eq86 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq200 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq200 eq86


@[equational_result]
theorem Equation14209_implies_Equation2 (G : Type*) [Magma G] (h : Equation14209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X5)) = X0 := superpose eq7 eq11
  have eq94 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq211 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq211 eq94


@[equational_result]
theorem Equation14210_implies_Equation2 (G : Type*) [Magma G] (h : Equation14210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation14212_implies_Equation2 (G : Type*) [Magma G] (h : Equation14212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X2 X5 : G) : (X5 ◇ (X2 ◇ X5)) = X0 := superpose eq7 eq11
  have eq102 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq215 eq102


@[equational_result]
theorem Equation14213_implies_Equation2 (G : Type*) [Magma G] (h : Equation14213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq76 eq14


