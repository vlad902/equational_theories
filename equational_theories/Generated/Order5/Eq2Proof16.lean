import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation33344_implies_Equation2 (G : Type*) [Magma G] (h : Equation33344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33346_implies_Equation2 (G : Type*) [Magma G] (h : Equation33346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X1) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq9
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq33 eq23


@[equational_result]
theorem Equation33348_implies_Equation2 (G : Type*) [Magma G] (h : Equation33348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33352_implies_Equation2 (G : Type*) [Magma G] (h : Equation33352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation33354_implies_Equation2 (G : Type*) [Magma G] (h : Equation33354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X4) ◇ X5)) ◇ X1) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq9
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq164 eq73


@[equational_result]
theorem Equation33355_implies_Equation2 (G : Type*) [Magma G] (h : Equation33355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X4)) ◇ X2) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq10
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq142 eq50


@[equational_result]
theorem Equation33356_implies_Equation2 (G : Type*) [Magma G] (h : Equation33356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X4) ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X4)) ◇ X4) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation33357_implies_Equation2 (G : Type*) [Magma G] (h : Equation33357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33359_implies_Equation2 (G : Type*) [Magma G] (h : Equation33359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq85 eq31


@[equational_result]
theorem Equation33361_implies_Equation2 (G : Type*) [Magma G] (h : Equation33361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33363_implies_Equation2 (G : Type*) [Magma G] (h : Equation33363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33364_implies_Equation2 (G : Type*) [Magma G] (h : Equation33364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33365_implies_Equation2 (G : Type*) [Magma G] (h : Equation33365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33367_implies_Equation2 (G : Type*) [Magma G] (h : Equation33367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33368_implies_Equation2 (G : Type*) [Magma G] (h : Equation33368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33369_implies_Equation2 (G : Type*) [Magma G] (h : Equation33369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33371_implies_Equation2 (G : Type*) [Magma G] (h : Equation33371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33372_implies_Equation2 (G : Type*) [Magma G] (h : Equation33372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33373_implies_Equation2 (G : Type*) [Magma G] (h : Equation33373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33374_implies_Equation2 (G : Type*) [Magma G] (h : Equation33374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33376_implies_Equation2 (G : Type*) [Magma G] (h : Equation33376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq26 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X3)) = X4 := superpose eq7 eq10
  have eq42 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq26
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq42
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq7 eq84
  have eq323 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq323 eq173


@[equational_result]
theorem Equation33378_implies_Equation2 (G : Type*) [Magma G] (h : Equation33378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation33380_implies_Equation2 (G : Type*) [Magma G] (h : Equation33380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33381_implies_Equation2 (G : Type*) [Magma G] (h : Equation33381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33382_implies_Equation2 (G : Type*) [Magma G] (h : Equation33382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33384_implies_Equation2 (G : Type*) [Magma G] (h : Equation33384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33385_implies_Equation2 (G : Type*) [Magma G] (h : Equation33385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33386_implies_Equation2 (G : Type*) [Magma G] (h : Equation33386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33388_implies_Equation2 (G : Type*) [Magma G] (h : Equation33388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33389_implies_Equation2 (G : Type*) [Magma G] (h : Equation33389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33390_implies_Equation2 (G : Type*) [Magma G] (h : Equation33390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33391_implies_Equation2 (G : Type*) [Magma G] (h : Equation33391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33393_implies_Equation2 (G : Type*) [Magma G] (h : Equation33393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq127 eq49


@[equational_result]
theorem Equation33394_implies_Equation2 (G : Type*) [Magma G] (h : Equation33394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation33395_implies_Equation2 (G : Type*) [Magma G] (h : Equation33395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X4) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X3 ◇ (X2 ◇ X1)) ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq9
  have eq21 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X4 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq43 eq26


@[equational_result]
theorem Equation33396_implies_Equation2 (G : Type*) [Magma G] (h : Equation33396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33398_implies_Equation2 (G : Type*) [Magma G] (h : Equation33398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33399_implies_Equation2 (G : Type*) [Magma G] (h : Equation33399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33400_implies_Equation2 (G : Type*) [Magma G] (h : Equation33400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33401_implies_Equation2 (G : Type*) [Magma G] (h : Equation33401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33403_implies_Equation2 (G : Type*) [Magma G] (h : Equation33403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33404_implies_Equation2 (G : Type*) [Magma G] (h : Equation33404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33405_implies_Equation2 (G : Type*) [Magma G] (h : Equation33405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33406_implies_Equation2 (G : Type*) [Magma G] (h : Equation33406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33408_implies_Equation2 (G : Type*) [Magma G] (h : Equation33408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33409_implies_Equation2 (G : Type*) [Magma G] (h : Equation33409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33410_implies_Equation2 (G : Type*) [Magma G] (h : Equation33410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33411_implies_Equation2 (G : Type*) [Magma G] (h : Equation33411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33413_implies_Equation2 (G : Type*) [Magma G] (h : Equation33413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33414_implies_Equation2 (G : Type*) [Magma G] (h : Equation33414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33415_implies_Equation2 (G : Type*) [Magma G] (h : Equation33415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33416_implies_Equation2 (G : Type*) [Magma G] (h : Equation33416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33417_implies_Equation2 (G : Type*) [Magma G] (h : Equation33417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33420_implies_Equation2 (G : Type*) [Magma G] (h : Equation33420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq45 eq11


@[equational_result]
theorem Equation33421_implies_Equation2 (G : Type*) [Magma G] (h : Equation33421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation33425_implies_Equation2 (G : Type*) [Magma G] (h : Equation33425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33428_implies_Equation2 (G : Type*) [Magma G] (h : Equation33428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq53 eq12


@[equational_result]
theorem Equation33429_implies_Equation2 (G : Type*) [Magma G] (h : Equation33429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation33431_implies_Equation2 (G : Type*) [Magma G] (h : Equation33431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (((X3 ◇ X3) ◇ X0) ◇ X4) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (((X4 ◇ X4) ◇ X0) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ X4) = (X0 ◇ X3) := superpose eq7 eq10
  have eq34 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq13
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X3) ◇ (((X4 ◇ X4) ◇ X0) ◇ X5))) = X2 := superpose eq34 eq11
  have eq43 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = X2 := superpose eq34 eq36
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq34 eq43
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq34 eq44
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation33432_implies_Equation2 (G : Type*) [Magma G] (h : Equation33432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq61 eq12


@[equational_result]
theorem Equation33433_implies_Equation2 (G : Type*) [Magma G] (h : Equation33433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation33434_implies_Equation2 (G : Type*) [Magma G] (h : Equation33434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33438_implies_Equation2 (G : Type*) [Magma G] (h : Equation33438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33440_implies_Equation2 (G : Type*) [Magma G] (h : Equation33440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33441_implies_Equation2 (G : Type*) [Magma G] (h : Equation33441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33442_implies_Equation2 (G : Type*) [Magma G] (h : Equation33442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33444_implies_Equation2 (G : Type*) [Magma G] (h : Equation33444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33445_implies_Equation2 (G : Type*) [Magma G] (h : Equation33445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33446_implies_Equation2 (G : Type*) [Magma G] (h : Equation33446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33448_implies_Equation2 (G : Type*) [Magma G] (h : Equation33448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33449_implies_Equation2 (G : Type*) [Magma G] (h : Equation33449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33450_implies_Equation2 (G : Type*) [Magma G] (h : Equation33450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33451_implies_Equation2 (G : Type*) [Magma G] (h : Equation33451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33453_implies_Equation2 (G : Type*) [Magma G] (h : Equation33453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq116 eq37


@[equational_result]
theorem Equation33454_implies_Equation2 (G : Type*) [Magma G] (h : Equation33454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq43 eq11


@[equational_result]
theorem Equation33455_implies_Equation2 (G : Type*) [Magma G] (h : Equation33455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation33457_implies_Equation2 (G : Type*) [Magma G] (h : Equation33457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33458_implies_Equation2 (G : Type*) [Magma G] (h : Equation33458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33459_implies_Equation2 (G : Type*) [Magma G] (h : Equation33459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33461_implies_Equation2 (G : Type*) [Magma G] (h : Equation33461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33462_implies_Equation2 (G : Type*) [Magma G] (h : Equation33462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33463_implies_Equation2 (G : Type*) [Magma G] (h : Equation33463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33465_implies_Equation2 (G : Type*) [Magma G] (h : Equation33465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33466_implies_Equation2 (G : Type*) [Magma G] (h : Equation33466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33467_implies_Equation2 (G : Type*) [Magma G] (h : Equation33467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33468_implies_Equation2 (G : Type*) [Magma G] (h : Equation33468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33470_implies_Equation2 (G : Type*) [Magma G] (h : Equation33470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq110 eq40


@[equational_result]
theorem Equation33471_implies_Equation2 (G : Type*) [Magma G] (h : Equation33471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation33472_implies_Equation2 (G : Type*) [Magma G] (h : Equation33472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation33473_implies_Equation2 (G : Type*) [Magma G] (h : Equation33473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33475_implies_Equation2 (G : Type*) [Magma G] (h : Equation33475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33476_implies_Equation2 (G : Type*) [Magma G] (h : Equation33476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33477_implies_Equation2 (G : Type*) [Magma G] (h : Equation33477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33478_implies_Equation2 (G : Type*) [Magma G] (h : Equation33478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33480_implies_Equation2 (G : Type*) [Magma G] (h : Equation33480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33481_implies_Equation2 (G : Type*) [Magma G] (h : Equation33481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33482_implies_Equation2 (G : Type*) [Magma G] (h : Equation33482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33483_implies_Equation2 (G : Type*) [Magma G] (h : Equation33483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33485_implies_Equation2 (G : Type*) [Magma G] (h : Equation33485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33486_implies_Equation2 (G : Type*) [Magma G] (h : Equation33486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33487_implies_Equation2 (G : Type*) [Magma G] (h : Equation33487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33488_implies_Equation2 (G : Type*) [Magma G] (h : Equation33488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33490_implies_Equation2 (G : Type*) [Magma G] (h : Equation33490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33491_implies_Equation2 (G : Type*) [Magma G] (h : Equation33491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33492_implies_Equation2 (G : Type*) [Magma G] (h : Equation33492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33493_implies_Equation2 (G : Type*) [Magma G] (h : Equation33493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33494_implies_Equation2 (G : Type*) [Magma G] (h : Equation33494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33496_implies_Equation2 (G : Type*) [Magma G] (h : Equation33496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq133 eq41


@[equational_result]
theorem Equation33497_implies_Equation2 (G : Type*) [Magma G] (h : Equation33497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation33498_implies_Equation2 (G : Type*) [Magma G] (h : Equation33498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33499_implies_Equation2 (G : Type*) [Magma G] (h : Equation33499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation33501_implies_Equation2 (G : Type*) [Magma G] (h : Equation33501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation33502_implies_Equation2 (G : Type*) [Magma G] (h : Equation33502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq53 eq17


@[equational_result]
theorem Equation33503_implies_Equation2 (G : Type*) [Magma G] (h : Equation33503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X1)) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (((X3 ◇ X4) ◇ X0) ◇ X2)) = X4 := superpose eq7 eq7
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq44 eq35


@[equational_result]
theorem Equation33504_implies_Equation2 (G : Type*) [Magma G] (h : Equation33504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33506_implies_Equation2 (G : Type*) [Magma G] (h : Equation33506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation33507_implies_Equation2 (G : Type*) [Magma G] (h : Equation33507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33508_implies_Equation2 (G : Type*) [Magma G] (h : Equation33508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation33509_implies_Equation2 (G : Type*) [Magma G] (h : Equation33509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33511_implies_Equation2 (G : Type*) [Magma G] (h : Equation33511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X2)) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) ◇ X1) = X2 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq9 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation33512_implies_Equation2 (G : Type*) [Magma G] (h : Equation33512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation33513_implies_Equation2 (G : Type*) [Magma G] (h : Equation33513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33514_implies_Equation2 (G : Type*) [Magma G] (h : Equation33514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33516_implies_Equation2 (G : Type*) [Magma G] (h : Equation33516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ (X0 ◇ X6)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation33517_implies_Equation2 (G : Type*) [Magma G] (h : Equation33517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33518_implies_Equation2 (G : Type*) [Magma G] (h : Equation33518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33519_implies_Equation2 (G : Type*) [Magma G] (h : Equation33519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33520_implies_Equation2 (G : Type*) [Magma G] (h : Equation33520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X9 : G) : (X0 ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33522_implies_Equation2 (G : Type*) [Magma G] (h : Equation33522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X1) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq102 eq35


@[equational_result]
theorem Equation33523_implies_Equation2 (G : Type*) [Magma G] (h : Equation33523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X0) ◇ X3) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 : G) : ((X4 ◇ X0) ◇ X3) = X1 := superpose eq10 eq11
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation33524_implies_Equation2 (G : Type*) [Magma G] (h : Equation33524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq9
  have eq21 (X0 X2 X4 : G) : ((X4 ◇ X0) ◇ X4) = X2 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq46 eq26


@[equational_result]
theorem Equation33525_implies_Equation2 (G : Type*) [Magma G] (h : Equation33525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation33527_implies_Equation2 (G : Type*) [Magma G] (h : Equation33527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33528_implies_Equation2 (G : Type*) [Magma G] (h : Equation33528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33529_implies_Equation2 (G : Type*) [Magma G] (h : Equation33529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33530_implies_Equation2 (G : Type*) [Magma G] (h : Equation33530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33532_implies_Equation2 (G : Type*) [Magma G] (h : Equation33532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33533_implies_Equation2 (G : Type*) [Magma G] (h : Equation33533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33534_implies_Equation2 (G : Type*) [Magma G] (h : Equation33534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33535_implies_Equation2 (G : Type*) [Magma G] (h : Equation33535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33537_implies_Equation2 (G : Type*) [Magma G] (h : Equation33537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33538_implies_Equation2 (G : Type*) [Magma G] (h : Equation33538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33539_implies_Equation2 (G : Type*) [Magma G] (h : Equation33539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33540_implies_Equation2 (G : Type*) [Magma G] (h : Equation33540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33542_implies_Equation2 (G : Type*) [Magma G] (h : Equation33542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33543_implies_Equation2 (G : Type*) [Magma G] (h : Equation33543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33544_implies_Equation2 (G : Type*) [Magma G] (h : Equation33544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33545_implies_Equation2 (G : Type*) [Magma G] (h : Equation33545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33546_implies_Equation2 (G : Type*) [Magma G] (h : Equation33546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33548_implies_Equation2 (G : Type*) [Magma G] (h : Equation33548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq163 eq67


@[equational_result]
theorem Equation33549_implies_Equation2 (G : Type*) [Magma G] (h : Equation33549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation33550_implies_Equation2 (G : Type*) [Magma G] (h : Equation33550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33551_implies_Equation2 (G : Type*) [Magma G] (h : Equation33551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation33553_implies_Equation2 (G : Type*) [Magma G] (h : Equation33553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33554_implies_Equation2 (G : Type*) [Magma G] (h : Equation33554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33555_implies_Equation2 (G : Type*) [Magma G] (h : Equation33555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33556_implies_Equation2 (G : Type*) [Magma G] (h : Equation33556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33558_implies_Equation2 (G : Type*) [Magma G] (h : Equation33558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33559_implies_Equation2 (G : Type*) [Magma G] (h : Equation33559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33560_implies_Equation2 (G : Type*) [Magma G] (h : Equation33560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33561_implies_Equation2 (G : Type*) [Magma G] (h : Equation33561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33563_implies_Equation2 (G : Type*) [Magma G] (h : Equation33563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33564_implies_Equation2 (G : Type*) [Magma G] (h : Equation33564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33565_implies_Equation2 (G : Type*) [Magma G] (h : Equation33565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33566_implies_Equation2 (G : Type*) [Magma G] (h : Equation33566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33568_implies_Equation2 (G : Type*) [Magma G] (h : Equation33568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33569_implies_Equation2 (G : Type*) [Magma G] (h : Equation33569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33570_implies_Equation2 (G : Type*) [Magma G] (h : Equation33570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33571_implies_Equation2 (G : Type*) [Magma G] (h : Equation33571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33572_implies_Equation2 (G : Type*) [Magma G] (h : Equation33572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33574_implies_Equation2 (G : Type*) [Magma G] (h : Equation33574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X1) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq140 eq41


@[equational_result]
theorem Equation33575_implies_Equation2 (G : Type*) [Magma G] (h : Equation33575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation33576_implies_Equation2 (G : Type*) [Magma G] (h : Equation33576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33577_implies_Equation2 (G : Type*) [Magma G] (h : Equation33577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33579_implies_Equation2 (G : Type*) [Magma G] (h : Equation33579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33580_implies_Equation2 (G : Type*) [Magma G] (h : Equation33580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33581_implies_Equation2 (G : Type*) [Magma G] (h : Equation33581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33582_implies_Equation2 (G : Type*) [Magma G] (h : Equation33582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33584_implies_Equation2 (G : Type*) [Magma G] (h : Equation33584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33585_implies_Equation2 (G : Type*) [Magma G] (h : Equation33585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33586_implies_Equation2 (G : Type*) [Magma G] (h : Equation33586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33587_implies_Equation2 (G : Type*) [Magma G] (h : Equation33587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33589_implies_Equation2 (G : Type*) [Magma G] (h : Equation33589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33590_implies_Equation2 (G : Type*) [Magma G] (h : Equation33590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33591_implies_Equation2 (G : Type*) [Magma G] (h : Equation33591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33592_implies_Equation2 (G : Type*) [Magma G] (h : Equation33592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33594_implies_Equation2 (G : Type*) [Magma G] (h : Equation33594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33595_implies_Equation2 (G : Type*) [Magma G] (h : Equation33595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33596_implies_Equation2 (G : Type*) [Magma G] (h : Equation33596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33597_implies_Equation2 (G : Type*) [Magma G] (h : Equation33597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33598_implies_Equation2 (G : Type*) [Magma G] (h : Equation33598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33600_implies_Equation2 (G : Type*) [Magma G] (h : Equation33600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation33601_implies_Equation2 (G : Type*) [Magma G] (h : Equation33601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33602_implies_Equation2 (G : Type*) [Magma G] (h : Equation33602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33603_implies_Equation2 (G : Type*) [Magma G] (h : Equation33603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation33604_implies_Equation2 (G : Type*) [Magma G] (h : Equation33604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33606_implies_Equation2 (G : Type*) [Magma G] (h : Equation33606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33607_implies_Equation2 (G : Type*) [Magma G] (h : Equation33607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33608_implies_Equation2 (G : Type*) [Magma G] (h : Equation33608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33609_implies_Equation2 (G : Type*) [Magma G] (h : Equation33609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33610_implies_Equation2 (G : Type*) [Magma G] (h : Equation33610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33612_implies_Equation2 (G : Type*) [Magma G] (h : Equation33612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33613_implies_Equation2 (G : Type*) [Magma G] (h : Equation33613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33614_implies_Equation2 (G : Type*) [Magma G] (h : Equation33614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33615_implies_Equation2 (G : Type*) [Magma G] (h : Equation33615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33616_implies_Equation2 (G : Type*) [Magma G] (h : Equation33616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33618_implies_Equation2 (G : Type*) [Magma G] (h : Equation33618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33619_implies_Equation2 (G : Type*) [Magma G] (h : Equation33619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33620_implies_Equation2 (G : Type*) [Magma G] (h : Equation33620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33621_implies_Equation2 (G : Type*) [Magma G] (h : Equation33621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33622_implies_Equation2 (G : Type*) [Magma G] (h : Equation33622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33624_implies_Equation2 (G : Type*) [Magma G] (h : Equation33624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33625_implies_Equation2 (G : Type*) [Magma G] (h : Equation33625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33626_implies_Equation2 (G : Type*) [Magma G] (h : Equation33626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33627_implies_Equation2 (G : Type*) [Magma G] (h : Equation33627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33628_implies_Equation2 (G : Type*) [Magma G] (h : Equation33628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33630_implies_Equation2 (G : Type*) [Magma G] (h : Equation33630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33631_implies_Equation2 (G : Type*) [Magma G] (h : Equation33631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33632_implies_Equation2 (G : Type*) [Magma G] (h : Equation33632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33633_implies_Equation2 (G : Type*) [Magma G] (h : Equation33633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33634_implies_Equation2 (G : Type*) [Magma G] (h : Equation33634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33635_implies_Equation2 (G : Type*) [Magma G] (h : Equation33635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33841_implies_Equation2 (G : Type*) [Magma G] (h : Equation33841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq117 eq45


@[equational_result]
theorem Equation33844_implies_Equation2 (G : Type*) [Magma G] (h : Equation33844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq37 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))))) ◇ X4) = X2 := superpose eq7 eq9
  have eq69 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq37
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq69
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq164 eq70


@[equational_result]
theorem Equation33846_implies_Equation2 (G : Type*) [Magma G] (h : Equation33846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4)))) = X1 := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq9 eq7
  have eq44 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq9 eq10
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ X2) := superpose eq7 eq10
  have eq84 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0)) = X2 := superpose eq58 eq7
  have eq109 (X0 X1 X4 : G) : (((X4 ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) = X0 := superpose eq7 eq20
  have eq152 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq109 eq109
  have eq188 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) = ((((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X2 ◇ (((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ (((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ X4)))) := superpose eq58 eq44
  have eq216 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4))) = ((X1 ◇ (((X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4))) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))))) ◇ X0) := superpose eq7 eq44
  have eq255 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq152
  have eq259 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq44 eq152
  have eq260 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq58 eq152
  have eq304 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) = ((((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X2 ◇ (((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ X2))) := superpose eq255 eq188
  have eq319 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) = ((((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq152 eq304
  have eq323 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq152 eq259
  have eq340 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4))) = ((X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq323 eq216
  have eq344 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X0)) = X1 := superpose eq340 eq14
  have eq387 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq344 eq109
  have eq389 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X0 := superpose eq344 eq152
  have eq401 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := superpose eq387 eq319
  have eq402 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0)) = X2 := superpose eq401 eq84
  have eq403 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq389 eq260
  have eq422 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq403 eq402
  have eq425 (X0 X2 : G) : X0 = X2 := superpose eq422 eq422
  have eq564 (X0 : G) : sK0 ≠ X0 := superpose eq425 eq8
  subsumption eq564 eq425


@[equational_result]
theorem Equation33847_implies_Equation2 (G : Type*) [Magma G] (h : Equation33847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq105 eq32


@[equational_result]
theorem Equation33848_implies_Equation2 (G : Type*) [Magma G] (h : Equation33848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq41 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq129 eq57


@[equational_result]
theorem Equation33851_implies_Equation2 (G : Type*) [Magma G] (h : Equation33851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq117 eq45


@[equational_result]
theorem Equation33854_implies_Equation2 (G : Type*) [Magma G] (h : Equation33854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq9
  have eq39 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq13
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq39
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq135 eq52


@[equational_result]
theorem Equation33858_implies_Equation2 (G : Type*) [Magma G] (h : Equation33858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq9
  have eq38 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq13
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq38
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq120 eq52


@[equational_result]
theorem Equation33860_implies_Equation2 (G : Type*) [Magma G] (h : Equation33860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X3 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X3 ◇ X0)))) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X3 ◇ X0))) ◇ (X4 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X3 ◇ X0))))))) = X1 := superpose eq7 eq9
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq17
  have eq98 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := superpose eq7 eq49
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq17 eq98
  have eq316 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X3 ◇ X0))) ◇ (X4 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X3 ◇ X0))))))) = X1 := superpose eq232 eq25
  have eq320 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X1 := superpose eq232 eq316
  have eq339 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq320 eq320
  have eq412 (X0 X2 : G) : X0 = X2 := superpose eq9 eq339
  have eq592 (X0 : G) : sK0 ≠ X0 := superpose eq412 eq8
  subsumption eq592 eq412


@[equational_result]
theorem Equation33861_implies_Equation2 (G : Type*) [Magma G] (h : Equation33861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq107 eq34


@[equational_result]
theorem Equation33862_implies_Equation2 (G : Type*) [Magma G] (h : Equation33862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X5) = X3 := superpose eq7 eq7
  have eq40 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq120 eq54


@[equational_result]
theorem Equation33864_implies_Equation2 (G : Type*) [Magma G] (h : Equation33864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1)))))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) = (((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))))) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X1 := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq10 eq10
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X0)))))) ◇ ((X0 ◇ X4) ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X0)))))))) = X0 := superpose eq9 eq16
  have eq43 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X0)))))) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq16
  have eq60 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X4) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq43 eq39
  have eq80 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) ◇ X2) = ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))))) := superpose eq11 eq16
  have eq91 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ (X1 ◇ X5))) := superpose eq13 eq13
  have eq113 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq16
  have eq136 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) = (((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ X1) := superpose eq113 eq11
  have eq137 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) = ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)))) := superpose eq113 eq80
  have eq151 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) := superpose eq60 eq137
  have eq155 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) = (((X2 ◇ X1) ◇ X0) ◇ X1) := superpose eq151 eq136
  have eq173 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2)))) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) := superpose eq155 eq155
  have eq181 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ X3) ◇ X2) := superpose eq7 eq155
  have eq192 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq155 eq7
  have eq199 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq155 eq7
  have eq213 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq173 eq199
  have eq214 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X1 := superpose eq192 eq213
  have eq215 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X2 ◇ X1) ◇ X0) ◇ X1) := superpose eq214 eq155
  have eq255 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) := superpose eq215 eq181
  have eq259 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq255 eq91
  have eq263 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X3 := superpose eq214 eq259
  have eq265 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq263 eq10
  have eq276 (X0 X3 : G) : X0 = X3 := superpose eq265 eq265
  have eq286 (X0 : G) : sK0 ≠ X0 := superpose eq276 eq8
  subsumption eq286 eq276


@[equational_result]
theorem Equation33866_implies_Equation2 (G : Type*) [Magma G] (h : Equation33866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ X4) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X3 := superpose eq12 eq7
  have eq32 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq10
  have eq54 (X1 X3 X5 : G) : (X1 ◇ X5) = X3 := superpose eq32 eq28
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq54
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq149 eq55


@[equational_result]
theorem Equation33869_implies_Equation2 (G : Type*) [Magma G] (h : Equation33869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq142 eq37


@[equational_result]
theorem Equation33870_implies_Equation2 (G : Type*) [Magma G] (h : Equation33870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq40 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq121 eq55


@[equational_result]
theorem Equation33872_implies_Equation2 (G : Type*) [Magma G] (h : Equation33872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X4 ◇ X5))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X1 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ (X4 ◇ X5)))) ◇ ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ (X4 ◇ X5))) ◇ (X6 ◇ X7)))) = X1 := superpose eq7 eq9
  have eq55 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ X1)) := superpose eq9 eq18
  have eq124 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4))) := superpose eq18 eq55
  have eq177 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ (X4 ◇ X5))) ◇ (X6 ◇ X7)))) = X1 := superpose eq124 eq29
  have eq179 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X1 := superpose eq124 eq177
  have eq269 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq179 eq179
  have eq403 (X0 X4 : G) : X0 = X4 := superpose eq9 eq269
  have eq541 (X0 : G) : sK0 ≠ X0 := superpose eq403 eq8
  subsumption eq541 eq403


@[equational_result]
theorem Equation33873_implies_Equation2 (G : Type*) [Magma G] (h : Equation33873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X2 ◇ (X4 ◇ X5))) ◇ X4) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq127 eq41


@[equational_result]
theorem Equation33874_implies_Equation2 (G : Type*) [Magma G] (h : Equation33874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq106 eq36


@[equational_result]
theorem Equation33875_implies_Equation2 (G : Type*) [Magma G] (h : Equation33875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X6))) ◇ X7) = X4 := superpose eq7 eq7
  have eq41 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq9
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq7 eq41
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq120 eq54


@[equational_result]
theorem Equation33878_implies_Equation2 (G : Type*) [Magma G] (h : Equation33878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation33881_implies_Equation2 (G : Type*) [Magma G] (h : Equation33881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq57 eq18


@[equational_result]
theorem Equation33885_implies_Equation2 (G : Type*) [Magma G] (h : Equation33885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq7 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation33888_implies_Equation2 (G : Type*) [Magma G] (h : Equation33888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation33891_implies_Equation2 (G : Type*) [Magma G] (h : Equation33891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq58 eq21


@[equational_result]
theorem Equation33893_implies_Equation2 (G : Type*) [Magma G] (h : Equation33893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq10
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq11
  have eq64 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq30 eq30
  have eq73 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq30 eq7
  have eq114 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) := superpose eq10 eq73
  have eq116 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq73
  have eq117 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq73
  have eq118 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq10 eq73
  have eq120 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := superpose eq19 eq73
  have eq135 (X0 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq116 eq19
  have eq136 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq116 eq30
  have eq154 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq116 eq120
  have eq186 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq117 eq135
  have eq215 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq154 eq186
  have eq216 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq136 eq215
  have eq217 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq216 eq64
  have eq240 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq217 eq114
  have eq242 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq217 eq118
  have eq288 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) := superpose eq217 eq242
  have eq290 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq288 eq11
  have eq312 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq288 eq240
  have eq313 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X1 := superpose eq290 eq312
  have eq314 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq313 eq7
  have eq697 (X0 X2 : G) : X0 = X2 := superpose eq314 eq314
  have eq699 (X0 : G) : sK0 ≠ X0 := superpose eq697 eq8
  subsumption eq699 eq697


@[equational_result]
theorem Equation33894_implies_Equation2 (G : Type*) [Magma G] (h : Equation33894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ (((X3 ◇ X2) ◇ X0) ◇ X1))) = (X3 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq11
  have eq20 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) ◇ X3) = X2 := superpose eq16 eq9
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X1 := superpose eq11 eq20
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq20 eq7
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X2) = X2 := superpose eq7 eq10
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X2) := superpose eq26 eq10
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) = X2 := superpose eq52 eq53
  have eq79 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq78 eq27
  have eq86 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq7 eq79
  have eq205 (X0 X3 : G) : X0 = X3 := superpose eq7 eq86
  have eq355 (X0 : G) : sK0 ≠ X0 := superpose eq205 eq8
  subsumption eq355 eq205


@[equational_result]
theorem Equation33895_implies_Equation2 (G : Type*) [Magma G] (h : Equation33895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq60 eq21


@[equational_result]
theorem Equation33897_implies_Equation2 (G : Type*) [Magma G] (h : Equation33897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq13
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq10 eq13
  have eq71 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((((((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X0)) := superpose eq10 eq11
  have eq100 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq37 eq13
  have eq109 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq37 eq10
  have eq110 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = ((X0 ◇ ((X1 ◇ X1) ◇ X3)) ◇ (X1 ◇ X1)) := superpose eq37 eq10
  have eq117 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq37 eq15
  have eq138 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))))) ◇ (X5 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2)))) ◇ (X0 ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))))) := superpose eq15 eq9
  have eq151 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq100 eq100
  have eq164 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X4)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) := superpose eq13 eq100
  have eq170 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq100 eq9
  have eq178 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) := superpose eq100 eq10
  have eq255 (X0 X1 X2 X3 X4 : G) : (((((((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((((((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X3) ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq71 eq100
  have eq260 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq37 eq109
  have eq281 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq260 eq255
  have eq282 (X0 X1 X2 X4 : G) : (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq260 eq164
  have eq292 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X0)) := superpose eq281 eq71
  have eq294 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X1 ◇ ((X1 ◇ X1) ◇ X4)) ◇ (X1 ◇ X1)) := superpose eq282 eq39
  have eq307 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ X1) := superpose eq260 eq294
  have eq309 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X0)) := superpose eq307 eq292
  have eq316 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X2 := superpose eq307 eq100
  have eq317 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = ((X0 ◇ X2) ◇ (X1 ◇ X1)) := superpose eq307 eq117
  have eq336 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = (((X1 ◇ X1) ◇ ((X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X4 ◇ (X1 ◇ X1)))) ◇ (X5 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)))) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X4 ◇ (X1 ◇ X1))))) := superpose eq307 eq138
  have eq347 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X3 := superpose eq307 eq151
  have eq349 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) ◇ X0)) := superpose eq307 eq309
  have eq350 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) := superpose eq307 eq349
  have eq365 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq316 eq110
  have eq367 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) = X1 := superpose eq365 eq178
  have eq368 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X1 := superpose eq316 eq317
  have eq371 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq367 eq336
  have eq376 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ X1) ◇ X2) := superpose eq371 eq350
  have eq383 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) := superpose eq376 eq170
  have eq388 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X2) := superpose eq371 eq383
  have eq395 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq347 eq260
  have eq398 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X2 := superpose eq395 eq316
  have eq416 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq398 eq388
  have eq419 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X1 := superpose eq416 eq368
  have eq426 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X1 := superpose eq416 eq419
  have eq427 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq416 eq426
  have eq428 (X0 X3 : G) : X0 = X3 := superpose eq427 eq427
  have eq430 (X0 : G) : sK0 ≠ X0 := superpose eq428 eq8
  subsumption eq430 eq428


@[equational_result]
theorem Equation33899_implies_Equation2 (G : Type*) [Magma G] (h : Equation33899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X4 ◇ X3))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq7 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation33901_implies_Equation2 (G : Type*) [Magma G] (h : Equation33901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ (X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))))))) ◇ (X5 ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ (X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))))))))) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ (X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))))))) := superpose eq9 eq9
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ X4)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))))) := superpose eq9 eq10
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X1 := superpose eq7 eq12
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq12
  have eq68 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3))) := superpose eq7 eq31
  have eq75 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = ((X1 ◇ X1) ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) ◇ X0)) := superpose eq10 eq31
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq31 eq12
  have eq86 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq31 eq9
  have eq87 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq31 eq7
  have eq92 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq31 eq10
  have eq95 (X0 X1 X2 X4 : G) : (X2 ◇ X2) = ((X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X0) ◇ X4)) ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) := superpose eq31 eq12
  have eq140 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq82 eq82
  have eq145 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X4)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) := superpose eq12 eq82
  have eq151 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := superpose eq82 eq14
  have eq221 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq87
  have eq222 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq87
  have eq223 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) = X1 := superpose eq14 eq87
  have eq245 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ (X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))))))) := superpose eq222 eq22
  have eq250 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))))) := superpose eq222 eq27
  have eq264 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq222 eq86
  have eq265 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq222 eq245
  have eq266 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq140 eq265
  have eq273 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq266 eq250
  have eq286 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq82 eq273
  have eq288 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))))) = ((((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))))))) := superpose eq7 eq273
  have eq292 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq273 eq273
  have eq338 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq273 eq7
  have eq357 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq221 eq286
  have eq361 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq357 eq264
  have eq363 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))))) = ((((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq266 eq288
  have eq364 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))))) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq223 eq363
  have eq365 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq266 eq364
  have eq376 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq151 eq292
  have eq377 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq140 eq376
  have eq378 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq10 eq377
  have eq392 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq378 eq338
  have eq393 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq361 eq392
  have eq395 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))))) = (X0 ◇ X0) := superpose eq393 eq266
  have eq407 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq393 eq365
  have eq414 (X0 X1 X2 X4 : G) : (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq407 eq145
  have eq449 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq414 eq68
  have eq459 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ X1) := superpose eq407 eq449
  have eq462 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq459 eq30
  have eq468 (X0 X1 X3 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) := superpose eq459 eq395
  have eq471 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq407 eq468
  have eq472 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq462 eq471
  have eq482 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq472 eq75
  have eq488 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = X0 := superpose eq462 eq482
  have eq490 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X1 := superpose eq488 eq223
  have eq519 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq488 eq490
  have eq524 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) := superpose eq519 eq95
  have eq526 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq519 eq222
  have eq527 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq526 eq524
  have eq528 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq526 eq92
  have eq543 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X2 ◇ X2)) := superpose eq526 eq527
  have eq544 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq526 eq543
  have eq545 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq526 eq528
  have eq546 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq526 eq545
  have eq588 (X0 X1 : G) : X0 = X1 := superpose eq544 eq546
  have eq593 (X0 : G) : sK0 ≠ X0 := superpose eq588 eq8
  subsumption eq593 eq588


@[equational_result]
theorem Equation33903_implies_Equation2 (G : Type*) [Magma G] (h : Equation33903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation33905_implies_Equation2 (G : Type*) [Magma G] (h : Equation33905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ X3) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = ((X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2))) ◇ X3) ◇ X0) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)))) = X3 := superpose eq9 eq7
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq11 eq9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = ((X1 ◇ (((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq11 eq9
  have eq34 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq11 eq7
  have eq36 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) ◇ (X1 ◇ X1)) := superpose eq11 eq7
  have eq52 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X2)) := superpose eq9 eq34
  have eq55 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq11 eq34
  have eq60 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X1)))) := superpose eq34 eq16
  have eq72 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq55 eq30
  have eq74 (X0 X2 : G) : (X2 ◇ X2) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq52 eq60
  have eq75 (X0 X2 : G) : (X2 ◇ X2) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq11 eq74
  have eq76 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq72 eq75
  have eq154 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((X1 ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq76 eq12
  have eq170 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq76 eq9
  have eq205 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq55 eq154
  have eq208 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq170 eq36
  have eq209 (X0 X1 X3 : G) : ((((X1 ◇ X1) ◇ X3) ◇ X0) ◇ (X1 ◇ X1)) = X3 := superpose eq208 eq10
  have eq210 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq208 eq11
  have eq241 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((X1 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq210 eq205
  have eq251 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq210 eq33
  have eq279 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) := superpose eq210 eq208
  have eq294 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((X1 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq210 eq241
  have eq314 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ (X2 ◇ X2)) := superpose eq279 eq251
  have eq321 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ (X3 ◇ X3)) ◇ (X2 ◇ X2)) := superpose eq210 eq314
  have eq365 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq209
  have eq371 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq12 eq209
  have eq386 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = X1 := superpose eq7 eq371
  have eq387 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = X1 := superpose eq210 eq386
  have eq388 (X1 X3 X4 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) = X1 := superpose eq321 eq387
  have eq389 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose eq388 eq294
  have eq390 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X1) = X1 := superpose eq389 eq365
  have eq395 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X1)) = X3 := superpose eq390 eq209
  have eq406 (X0 X3 : G) : X0 = X3 := superpose eq7 eq395
  have eq464 (X0 : G) : sK0 ≠ X0 := superpose eq406 eq8
  subsumption eq464 eq406


@[equational_result]
theorem Equation33906_implies_Equation2 (G : Type*) [Magma G] (h : Equation33906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq7 eq9
  have eq43 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq18 eq18
  have eq64 (X0 X1 X2 : G) : (((((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq18 eq10
  have eq73 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = X2 := superpose eq43 eq64
  have eq106 (X0 X3 : G) : X0 = X3 := superpose eq73 eq73
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq206 eq106


@[equational_result]
theorem Equation33907_implies_Equation2 (G : Type*) [Magma G] (h : Equation33907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation33909_implies_Equation2 (G : Type*) [Magma G] (h : Equation33909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X5) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = ((X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ (X6 ◇ X7))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)))) := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = ((X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ X6)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)))) := superpose eq9 eq10
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq13
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : ((((((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) ◇ X0) ◇ X5) ◇ X4) ◇ (((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) ◇ X0)) = X5 := superpose eq13 eq11
  have eq92 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ X6))) := superpose eq9 eq39
  have eq105 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq39 eq13
  have eq107 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq39 eq9
  have eq158 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq105 eq105
  have eq179 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) = X0 := superpose eq105 eq13
  have eq182 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq105 eq7
  have eq198 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq158 eq107
  have eq289 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq198 eq198
  have eq319 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) = (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ X6))) := superpose eq289 eq92
  have eq327 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq289 eq182
  have eq374 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq327 eq24
  have eq407 (X0 X1 X4 X5 X6 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X5))) ◇ X6)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X5)))) := superpose eq374 eq37
  have eq415 (X0 X1 X4 X5 X6 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X5))) = ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X5))) ◇ X6))) := superpose eq374 eq319
  have eq417 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X5))) := superpose eq374 eq415
  have eq419 (X0 X1 X6 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X6)) ◇ (X0 ◇ X1)) := superpose eq417 eq407
  have eq421 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = X0 := superpose eq419 eq179
  have eq422 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq421 eq419
  have eq423 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) ◇ X0) ◇ X4) ◇ (((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) ◇ X0)) = X5 := superpose eq422 eq77
  have eq458 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) ◇ X4) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) = X5 := superpose eq422 eq423
  have eq459 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3))) = X5 := superpose eq422 eq458
  have eq460 (X1 X4 X5 : G) : ((X1 ◇ X4) ◇ X1) = X5 := superpose eq422 eq459
  have eq461 (X1 X5 : G) : (X1 ◇ X1) = X5 := superpose eq422 eq460
  have eq588 (X0 X1 : G) : X0 = X1 := superpose eq422 eq461
  have eq598 (X0 : G) : sK0 ≠ X0 := superpose eq588 eq8
  subsumption eq598 eq588


@[equational_result]
theorem Equation33910_implies_Equation2 (G : Type*) [Magma G] (h : Equation33910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ X4) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) = (X0 ◇ X2) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X4) = X3 := superpose eq12 eq7
  have eq25 (X0 X2 X4 : G) : ((X0 ◇ X0) ◇ X4) = X2 := superpose eq22 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq53 eq30


@[equational_result]
theorem Equation33911_implies_Equation2 (G : Type*) [Magma G] (h : Equation33911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5))) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X5) = X3 := superpose eq10 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation33912_implies_Equation2 (G : Type*) [Magma G] (h : Equation33912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X5 ◇ X6))) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : ((X0 ◇ X0) ◇ X7) = X4 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation33914_implies_Equation2 (G : Type*) [Magma G] (h : Equation33914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq10 eq10
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq9 eq15
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq95 eq41


@[equational_result]
theorem Equation33915_implies_Equation2 (G : Type*) [Magma G] (h : Equation33915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq99 eq29


@[equational_result]
theorem Equation33916_implies_Equation2 (G : Type*) [Magma G] (h : Equation33916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq111 eq47


@[equational_result]
theorem Equation33918_implies_Equation2 (G : Type*) [Magma G] (h : Equation33918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq96 eq48


@[equational_result]
theorem Equation33920_implies_Equation2 (G : Type*) [Magma G] (h : Equation33920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq142 eq49


@[equational_result]
theorem Equation33922_implies_Equation2 (G : Type*) [Magma G] (h : Equation33922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X1 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) = (((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3)))) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)))) = X0 := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X3))) = (((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ (((X0 ◇ X2) ◇ (X4 ◇ (X2 ◇ X4))) ◇ X0)) ◇ X1) := superpose eq9 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X3))) = (((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X2) ◇ X1) := superpose eq7 eq21
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) := superpose eq11 eq11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ X1)) := superpose eq9 eq11
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq31
  have eq99 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq43
  have eq106 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq43 eq43
  have eq111 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ X0)) := superpose eq43 eq11
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) = X1 := superpose eq43 eq9
  have eq133 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) := superpose eq106 eq111
  have eq134 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) := superpose eq43 eq133
  have eq148 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X0 := superpose eq99 eq7
  have eq156 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq99 eq10
  have eq238 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) ◇ (X4 ◇ (X5 ◇ X4))) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))))) = X5 := superpose eq25 eq9
  have eq278 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose eq43 eq148
  have eq282 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq148 eq25
  have eq284 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq148 eq11
  have eq303 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq43 eq282
  have eq307 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) = X0 := superpose eq284 eq15
  have eq314 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) = X0 := superpose eq284 eq307
  have eq315 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq284 eq314
  have eq323 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2))) := superpose eq43 eq315
  have eq331 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq11 eq315
  have eq400 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq331 eq29
  have eq401 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq400 eq331
  have eq404 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq401 eq106
  have eq405 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = (((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq401 eq156
  have eq407 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq401 eq134
  have eq445 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq404 eq323
  have eq447 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq401 eq445
  have eq448 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq447 eq43
  have eq450 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) = X1 := superpose eq448 eq112
  have eq457 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq448 eq278
  have eq458 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq448 eq303
  have eq469 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq457 eq405
  have eq510 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq469 eq450
  have eq528 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq448 eq407
  have eq529 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq457 eq528
  have eq543 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) ◇ (X4 ◇ (X5 ◇ X4))) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X5 := superpose eq529 eq238
  have eq548 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq529 eq284
  have eq617 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) ◇ (X5 ◇ X4)) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X5 := superpose eq529 eq543
  have eq619 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq548 eq510
  have eq621 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq619 eq458
  have eq629 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq457 eq621
  have eq631 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X5 := superpose eq629 eq617
  have eq665 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1)))) = X5 := superpose eq629 eq631
  have eq666 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X4) ◇ (X0 ◇ (X2 ◇ X1))) = X5 := superpose eq629 eq665
  have eq667 (X1 X2 X4 X5 : G) : ((X5 ◇ X4) ◇ (X2 ◇ X1)) = X5 := superpose eq629 eq666
  have eq668 (X1 X4 X5 : G) : ((X5 ◇ X4) ◇ X1) = X5 := superpose eq629 eq667
  have eq669 (X1 X4 X5 : G) : (X4 ◇ X1) = X5 := superpose eq629 eq668
  have eq670 (X0 X3 : G) : X0 = X3 := superpose eq669 eq669
  have eq682 (X0 : G) : sK0 ≠ X0 := superpose eq670 eq8
  subsumption eq682 eq670


@[equational_result]
theorem Equation33923_implies_Equation2 (G : Type*) [Magma G] (h : Equation33923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq146 eq38


@[equational_result]
theorem Equation33924_implies_Equation2 (G : Type*) [Magma G] (h : Equation33924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq114 eq49


@[equational_result]
theorem Equation33926_implies_Equation2 (G : Type*) [Magma G] (h : Equation33926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X1 ◇ X5))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq9 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq131 eq53


@[equational_result]
theorem Equation33927_implies_Equation2 (G : Type*) [Magma G] (h : Equation33927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X2 ◇ X5))) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq141 eq47


@[equational_result]
theorem Equation33928_implies_Equation2 (G : Type*) [Magma G] (h : Equation33928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X3 ◇ X5))) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq9
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq36 eq29


@[equational_result]
theorem Equation33929_implies_Equation2 (G : Type*) [Magma G] (h : Equation33929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X7) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq115 eq50


@[equational_result]
theorem Equation33931_implies_Equation2 (G : Type*) [Magma G] (h : Equation33931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq10 eq10
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq9 eq14
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq108 eq37


@[equational_result]
theorem Equation33932_implies_Equation2 (G : Type*) [Magma G] (h : Equation33932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation33933_implies_Equation2 (G : Type*) [Magma G] (h : Equation33933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq45 eq18


@[equational_result]
theorem Equation33935_implies_Equation2 (G : Type*) [Magma G] (h : Equation33935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq80 eq41


@[equational_result]
theorem Equation33937_implies_Equation2 (G : Type*) [Magma G] (h : Equation33937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation33939_implies_Equation2 (G : Type*) [Magma G] (h : Equation33939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq9 eq7
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq11 eq10
  have eq70 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) = X1 := superpose eq11 eq53
  have eq101 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) = X3 := superpose eq17 eq9
  have eq110 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq70 eq101
  have eq118 (X0 X2 : G) : X0 = X2 := superpose eq11 eq110
  have eq285 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq285 eq118


@[equational_result]
theorem Equation33940_implies_Equation2 (G : Type*) [Magma G] (h : Equation33940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X2 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq44 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq7 eq18
  have eq52 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq18 eq7
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))) = ((X0 ◇ X1) ◇ X0) := superpose eq18 eq10
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X2) = X0 := superpose eq18 eq7
  have eq63 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq18 eq52
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X1 := superpose eq63 eq36
  have eq65 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ X1) := superpose eq53 eq44
  have eq66 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq65 eq7
  have eq99 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq66 eq66
  have eq101 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq18 eq63
  have eq102 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq63 eq63
  have eq105 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq102 eq65
  have eq129 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq102 eq99
  have eq132 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq63 eq129
  have eq145 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X1 := superpose eq101 eq63
  have eq156 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) = X1 := superpose eq102 eq145
  have eq157 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := superpose eq105 eq156
  have eq158 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq157 eq132
  have eq159 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq158 eq18
  have eq161 (X0 X2 : G) : ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) = X0 := superpose eq158 eq54
  have eq204 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq158 eq161
  have eq205 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq159 eq204
  have eq206 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq205 eq64
  have eq208 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X1 := superpose eq205 eq206
  have eq209 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq205 eq208
  have eq213 (X0 X1 : G) : X0 = X1 := superpose eq209 eq205
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq213 eq8
  subsumption eq215 eq213


@[equational_result]
theorem Equation33941_implies_Equation2 (G : Type*) [Magma G] (h : Equation33941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation33943_implies_Equation2 (G : Type*) [Magma G] (h : Equation33943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq102 eq49


@[equational_result]
theorem Equation33944_implies_Equation2 (G : Type*) [Magma G] (h : Equation33944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X1 ◇ X4)) = (X0 ◇ X2) := superpose eq7 eq7
  have eq21 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq12
  have eq27 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq21 eq10
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation33945_implies_Equation2 (G : Type*) [Magma G] (h : Equation33945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ (X5 ◇ X0)) ◇ X3) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X5 ◇ X0)) ◇ X3) = X4 := superpose eq11 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation33946_implies_Equation2 (G : Type*) [Magma G] (h : Equation33946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X7) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq51 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation33949_implies_Equation2 (G : Type*) [Magma G] (h : Equation33949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq104 eq32


@[equational_result]
theorem Equation33950_implies_Equation2 (G : Type*) [Magma G] (h : Equation33950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X4) := superpose eq7 eq7
  have eq17 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq115 eq50


@[equational_result]
theorem Equation33954_implies_Equation2 (G : Type*) [Magma G] (h : Equation33954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X2 ◇ (X2 ◇ X1)) = (X0 ◇ X4) := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq12
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq164 eq50


@[equational_result]
theorem Equation33956_implies_Equation2 (G : Type*) [Magma G] (h : Equation33956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq23 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq10 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X3 ◇ X3)))) = X2 := superpose eq10 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X3 ◇ X3))) = ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X4 ◇ (X4 ◇ X4)))) := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X4 ◇ (X4 ◇ X4)))) = X2 := superpose eq10 eq9
  have eq40 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X3)))) = X2 := superpose eq23 eq30
  have eq41 (X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X4 ◇ (X4 ◇ X4))) = X2 := superpose eq23 eq34
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) := superpose eq17 eq7
  have eq71 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X2 ◇ X2)) ◇ X1) := superpose eq23 eq59
  have eq201 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) := superpose eq71 eq71
  have eq210 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X3 ◇ X3)))) = X1 := superpose eq71 eq9
  have eq211 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) = X1 := superpose eq71 eq7
  have eq347 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := superpose eq9 eq201
  have eq406 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := superpose eq23 eq347
  have eq2223 (X0 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X3))) = ((X0 ◇ (X4 ◇ (X4 ◇ X4))) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X3)))) := superpose eq40 eq211
  have eq6582 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq31
  have eq6607 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ X4)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := superpose eq31 eq40
  have eq6701 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))))) ◇ ((X3 ◇ (X4 ◇ (X4 ◇ X4))) ◇ (X5 ◇ (X5 ◇ X5)))) = X3 := superpose eq31 eq40
  have eq6904 (X0 X1 X2 X4 : G) : ((X4 ◇ (X4 ◇ X4)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = X0 := superpose eq6582 eq6607
  have eq6962 (X0 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ (X4 ◇ (X4 ◇ X4))) ◇ (X5 ◇ (X5 ◇ X5)))) = X3 := superpose eq6904 eq6701
  have eq6963 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := superpose eq6962 eq2223
  have eq6965 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq6963 eq406
  have eq7002 (X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X4))) = X2 := superpose eq6965 eq41
  have eq7009 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X3 ◇ X3)))) = X1 := superpose eq6965 eq210
  have eq7294 (X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) = X2 := superpose eq6965 eq7002
  have eq7295 (X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) = X2 := superpose eq6965 eq7294
  have eq7296 (X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq6965 eq7295
  have eq7297 (X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq6965 eq7296
  have eq7298 (X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq6965 eq7297
  have eq7301 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X1 := superpose eq7298 eq7009
  have eq7302 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X1 := superpose eq6965 eq7301
  have eq7303 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq6965 eq7302
  have eq7304 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq7303 eq7298
  have eq7308 (X0 X3 : G) : X0 = X3 := superpose eq7304 eq7304
  have eq7327 (X0 : G) : sK0 ≠ X0 := superpose eq7308 eq8
  subsumption eq7327 eq7308


@[equational_result]
theorem Equation33957_implies_Equation2 (G : Type*) [Magma G] (h : Equation33957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation33958_implies_Equation2 (G : Type*) [Magma G] (h : Equation33958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ X4) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq129 eq47


@[equational_result]
theorem Equation33960_implies_Equation2 (G : Type*) [Magma G] (h : Equation33960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X4 ◇ X5))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq9
  have eq80 (X0 X3 : G) : X0 = X3 := superpose eq61 eq61
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq176 eq80


@[equational_result]
theorem Equation33961_implies_Equation2 (G : Type*) [Magma G] (h : Equation33961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X4 ◇ X5))) ◇ X4) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation33962_implies_Equation2 (G : Type*) [Magma G] (h : Equation33962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X4 ◇ X5))) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation33963_implies_Equation2 (G : Type*) [Magma G] (h : Equation33963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 X6 : G) : (X2 ◇ (X2 ◇ X3)) = (X0 ◇ X6) := superpose eq7 eq7
  have eq17 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq134 eq50


@[equational_result]
theorem Equation33965_implies_Equation2 (G : Type*) [Magma G] (h : Equation33965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq119 eq41


@[equational_result]
theorem Equation33966_implies_Equation2 (G : Type*) [Magma G] (h : Equation33966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X2))) ◇ X4) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation33967_implies_Equation2 (G : Type*) [Magma G] (h : Equation33967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X3))) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq11 eq9
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq36 eq29


@[equational_result]
theorem Equation33968_implies_Equation2 (G : Type*) [Magma G] (h : Equation33968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X7) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq114 eq49


@[equational_result]
theorem Equation33970_implies_Equation2 (G : Type*) [Magma G] (h : Equation33970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq106 eq38


@[equational_result]
theorem Equation33971_implies_Equation2 (G : Type*) [Magma G] (h : Equation33971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1)))))) ◇ X4) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X4 ◇ X1)) = (X0 ◇ X2) := superpose eq7 eq7
  have eq36 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq12
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ (X3 ◇ X1)))) ◇ X4) = X2 := superpose eq36 eq9
  have eq57 (X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X3 ◇ X1)) ◇ X4) = X2 := superpose eq36 eq47
  have eq58 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq36 eq57
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq61 eq59


@[equational_result]
theorem Equation33972_implies_Equation2 (G : Type*) [Magma G] (h : Equation33972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq131 eq43


@[equational_result]
theorem Equation33973_implies_Equation2 (G : Type*) [Magma G] (h : Equation33973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X7) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation33975_implies_Equation2 (G : Type*) [Magma G] (h : Equation33975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X4))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq60 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq14 eq14
  have eq133 (X0 X3 : G) : X0 = X3 := superpose eq9 eq60
  have eq267 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq267 eq133


@[equational_result]
theorem Equation33976_implies_Equation2 (G : Type*) [Magma G] (h : Equation33976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X4))) ◇ X4) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation33977_implies_Equation2 (G : Type*) [Magma G] (h : Equation33977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation33978_implies_Equation2 (G : Type*) [Magma G] (h : Equation33978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X7) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation33980_implies_Equation2 (G : Type*) [Magma G] (h : Equation33980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X4)) = (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3)))) = X1 := superpose eq7 eq10
  have eq44 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X2) = (((X0 ◇ (X1 ◇ X1)) ◇ X5) ◇ X2) := superpose eq11 eq10
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = X2 := superpose eq11 eq7
  have eq48 (X0 X1 X2 X5 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X5) ◇ X2) = X2 := superpose eq46 eq44
  have eq52 (X2 X5 : G) : (X5 ◇ X2) = X2 := superpose eq46 eq48
  have eq53 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ (X3 ◇ X3))) = X1 := superpose eq52 eq12
  have eq62 (X0 X1 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X3)) = X1 := superpose eq52 eq53
  have eq63 (X0 X1 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X1 := superpose eq52 eq62
  have eq64 (X1 X3 X4 : G) : (X4 ◇ X3) = X1 := superpose eq52 eq63
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq64 eq64
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq70 eq65


@[equational_result]
theorem Equation33981_implies_Equation2 (G : Type*) [Magma G] (h : Equation33981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X5))) ◇ X4) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq70 eq19


@[equational_result]
theorem Equation33982_implies_Equation2 (G : Type*) [Magma G] (h : Equation33982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X5))) ◇ X5) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation33983_implies_Equation2 (G : Type*) [Magma G] (h : Equation33983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X7) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation33985_implies_Equation2 (G : Type*) [Magma G] (h : Equation33985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq128 eq41


@[equational_result]
theorem Equation33986_implies_Equation2 (G : Type*) [Magma G] (h : Equation33986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ (X6 ◇ X7))) ◇ X5) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation33987_implies_Equation2 (G : Type*) [Magma G] (h : Equation33987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ (X6 ◇ X7))) ◇ X6) = X3 := superpose eq7 eq7
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq53 eq33


@[equational_result]
theorem Equation33988_implies_Equation2 (G : Type*) [Magma G] (h : Equation33988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ (X6 ◇ X7))) ◇ X7) = X4 := superpose eq7 eq7
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq53 eq33


@[equational_result]
theorem Equation33989_implies_Equation2 (G : Type*) [Magma G] (h : Equation33989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X9 : G) : (((X1 ◇ X2) ◇ X0) ◇ X9) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation33992_implies_Equation2 (G : Type*) [Magma G] (h : Equation33992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq165 eq59


@[equational_result]
theorem Equation33995_implies_Equation2 (G : Type*) [Magma G] (h : Equation33995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) ◇ X3) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ (X1 ◇ X4)) ◇ ((X1 ◇ (X1 ◇ X4)) ◇ X3))) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X5) := superpose eq12 eq12
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := superpose eq7 eq12
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) ◇ X3) := superpose eq12 eq7
  have eq39 (X0 X1 X2 X5 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X5) = X1 := superpose eq27 eq26
  have eq42 (X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ X3) := superpose eq39 eq31
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ X3) = X2 := superpose eq42 eq9
  have eq60 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq42 eq47
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq60 eq60
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq71 eq69


@[equational_result]
theorem Equation33997_implies_Equation2 (G : Type*) [Magma G] (h : Equation33997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq9
  have eq18 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X3 ◇ X3) ◇ X1) ◇ X3) := superpose eq12 eq12
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq7 eq12
  have eq23 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq12 eq7
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq23 eq23
  have eq36 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq23
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq36 eq19
  have eq88 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := superpose eq34 eq7
  have eq92 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq34 eq88
  have eq218 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq92 eq18
  have eq367 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq36 eq36
  have eq391 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = X2 := superpose eq36 eq23
  have eq397 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq36 eq12
  have eq403 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq7 eq397
  have eq424 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq46 eq46
  have eq442 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq36 eq424
  have eq452 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq442 eq218
  have eq569 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose eq442 eq452
  have eq570 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq442 eq569
  have eq571 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq442 eq570
  have eq574 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq571 eq367
  have eq575 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq571 eq403
  have eq584 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq442 eq574
  have eq590 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq584 eq391
  have eq595 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq575 eq584
  have eq598 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X2 := superpose eq595 eq590
  have eq604 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq595 eq598
  have eq676 (X0 X1 : G) : X0 = X1 := superpose eq595 eq604
  have eq681 (X0 : G) : sK0 ≠ X0 := superpose eq676 eq8
  subsumption eq681 eq676


@[equational_result]
theorem Equation33999_implies_Equation2 (G : Type*) [Magma G] (h : Equation33999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq177 eq65


@[equational_result]
theorem Equation34002_implies_Equation2 (G : Type*) [Magma G] (h : Equation34002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq12
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq153 eq56


@[equational_result]
theorem Equation34005_implies_Equation2 (G : Type*) [Magma G] (h : Equation34005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq135 eq46


@[equational_result]
theorem Equation34007_implies_Equation2 (G : Type*) [Magma G] (h : Equation34007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq13 eq9
  have eq23 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X4)))) := superpose eq10 eq20
  have eq36 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X4)))) := superpose eq17 eq23
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq7 eq17
  have eq39 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq17 eq17
  have eq43 (X0 X1 X2 : G) : (((((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq17 eq17
  have eq144 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ X4)) := superpose eq17 eq38
  have eq150 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X4)) := superpose eq10 eq38
  have eq190 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq38 eq7
  have eq258 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0)) = (((X3 ◇ X3) ◇ (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ X3) ◇ (X1 ◇ X2))) ◇ X3) := superpose eq18 eq18
  have eq264 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) = (((X4 ◇ X4) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X4) ◇ (X0 ◇ X0))) ◇ X4) := superpose eq36 eq18
  have eq273 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = (((X4 ◇ X4) ◇ (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ X4) ◇ (X1 ◇ X2))) ◇ X4) := superpose eq18 eq18
  have eq279 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq18 eq18
  have eq286 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq17 eq18
  have eq295 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq18
  have eq310 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0)) ◇ X1) := superpose eq18 eq7
  have eq346 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = (((X3 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ (X1 ◇ X2))) ◇ X3) := superpose eq190 eq258
  have eq353 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = (((X4 ◇ X4) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X4) ◇ (X1 ◇ X2))) ◇ X4) := superpose eq190 eq273
  have eq355 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq144 eq279
  have eq356 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq190 eq355
  have eq361 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq190 eq286
  have eq363 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ (X1 ◇ X2))) ◇ X3) = X1 := superpose eq361 eq346
  have eq371 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq363 eq353
  have eq373 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := superpose eq363 eq264
  have eq374 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq371 eq43
  have eq413 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq371 eq295
  have eq427 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) := superpose eq190 eq310
  have eq428 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ X2) := superpose eq39 eq427
  have eq429 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq428 eq356
  have eq434 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq413 eq429
  have eq442 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X4)) := superpose eq434 eq150
  have eq467 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) = X0 := superpose eq442 eq373
  have eq476 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq467 eq374
  have eq477 (X0 X3 : G) : X0 = X3 := superpose eq17 eq476
  have eq523 (X0 : G) : sK0 ≠ X0 := superpose eq477 eq8
  subsumption eq523 eq477


@[equational_result]
theorem Equation34008_implies_Equation2 (G : Type*) [Magma G] (h : Equation34008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((((X5 ◇ X5) ◇ (X5 ◇ X5)) ◇ X4) ◇ (X1 ◇ (X5 ◇ (X0 ◇ X2)))) = ((X3 ◇ X3) ◇ (X4 ◇ (X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X4) ◇ (X3 ◇ (X0 ◇ X2))) = (((X3 ◇ X3) ◇ (X3 ◇ X3)) ◇ (X4 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ (X4 ◇ (X3 ◇ (((X2 ◇ X2) ◇ X1) ◇ X5)))) = ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))))) ◇ X4) ◇ X5) := superpose eq10 eq10
  have eq28 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq10 eq7
  have eq30 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X3) ◇ (X3 ◇ X3)) ◇ (X4 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2)))) = X4 := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 X4 : G) : (((((X2 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))))) ◇ X3) = X4 := superpose eq10 eq7
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : (((((((X2 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))))) ◇ ((((X2 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))))) ◇ (X5 ◇ X4)) ◇ X3) = X5 := superpose eq10 eq9
  have eq68 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X4) ◇ (X3 ◇ X4)) := superpose eq10 eq28
  have eq91 (X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1)))) ◇ (X5 ◇ X4)) ◇ X3) = X5 := superpose eq68 eq38
  have eq95 (X1 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (X5 ◇ X4)) ◇ X3) = X5 := superpose eq28 eq91
  have eq96 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ (X4 ◇ (X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)))) = (X5 ◇ (X1 ◇ (X5 ◇ (X0 ◇ X2)))) := superpose eq95 eq14
  have eq98 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ (X4 ◇ (X3 ◇ (((X2 ◇ X2) ◇ X1) ◇ X5)))) = (X1 ◇ X5) := superpose eq95 eq22
  have eq102 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2)))) = X4 := superpose eq95 eq30
  have eq103 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X4) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq95 eq17
  have eq117 (X0 X1 X2 X5 : G) : (X1 ◇ X2) = (X5 ◇ (X1 ◇ (X5 ◇ (X0 ◇ X2)))) := superpose eq98 eq96
  have eq118 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq103 eq29
  have eq120 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X2) ◇ X1) ◇ (X4 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))))) ◇ X3) = X4 := superpose eq118 eq34
  have eq145 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq118 eq103
  have eq146 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X2) ◇ X1) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))))) ◇ X3) = X4 := superpose eq118 eq120
  have eq147 (X1 X2 X3 X4 : G) : ((((X2 ◇ X2) ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) ◇ X3) = X4 := superpose eq117 eq146
  have eq148 (X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) ◇ X3) = X4 := superpose eq118 eq147
  have eq176 (X3 X4 : G) : (X4 ◇ X3) = X4 := superpose eq145 eq148
  have eq178 (X1 X3 X4 : G) : (X3 ◇ (X1 ◇ X3)) = X4 := superpose eq176 eq102
  have eq195 (X1 X3 X4 : G) : (X3 ◇ X1) = X4 := superpose eq176 eq178
  have eq196 (X0 X1 : G) : X0 = X1 := superpose eq118 eq195
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq196 eq8
  subsumption eq204 eq196


@[equational_result]
theorem Equation34009_implies_Equation2 (G : Type*) [Magma G] (h : Equation34009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq9
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq12
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq153 eq56


@[equational_result]
theorem Equation34011_implies_Equation2 (G : Type*) [Magma G] (h : Equation34011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq17
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq21 eq7
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq55 eq48


@[equational_result]
theorem Equation34013_implies_Equation2 (G : Type*) [Magma G] (h : Equation34013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq138 eq37


@[equational_result]
theorem Equation34015_implies_Equation2 (G : Type*) [Magma G] (h : Equation34015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X1 := superpose eq10 eq7
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq13
  have eq39 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq13 eq10
  have eq46 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq9 eq39
  have eq60 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq25
  have eq80 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq60 eq46
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) = X0 := superpose eq80 eq7
  have eq91 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq80 eq36
  have eq105 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq80 eq91
  have eq110 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq105 eq83
  have eq121 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq105 eq110
  have eq124 (X0 X2 : G) : X0 = X2 := superpose eq121 eq121
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq126 eq124


@[equational_result]
theorem Equation34017_implies_Equation2 (G : Type*) [Magma G] (h : Equation34017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq10 eq10
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq157 eq60


@[equational_result]
theorem Equation34019_implies_Equation2 (G : Type*) [Magma G] (h : Equation34019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3))) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := superpose eq7 eq9
  have eq35 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq21 eq10
  have eq39 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0)) := superpose eq9 eq35
  have eq45 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := superpose eq7 eq39
  have eq46 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq7 eq45
  have eq47 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq46 eq9
  have eq57 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := superpose eq46 eq24
  have eq96 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ (X5 ◇ X5))) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) := superpose eq47 eq47
  have eq122 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq47 eq7
  have eq126 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq57 eq96
  have eq134 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X1 ◇ X1)) = X2 := superpose eq46 eq122
  have eq135 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X2 := superpose eq126 eq134
  have eq140 (X0 X2 : G) : X0 = X2 := superpose eq135 eq135
  have eq200 (X0 : G) : sK0 ≠ X0 := superpose eq140 eq8
  subsumption eq200 eq140


@[equational_result]
theorem Equation34020_implies_Equation2 (G : Type*) [Magma G] (h : Equation34020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq10 eq7
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq156 eq49


@[equational_result]
theorem Equation34021_implies_Equation2 (G : Type*) [Magma G] (h : Equation34021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = X1 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation34023_implies_Equation2 (G : Type*) [Magma G] (h : Equation34023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq11
  have eq40 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq24 eq7
  have eq51 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq14 eq40
  have eq80 (X0 X2 : G) : X0 = X2 := superpose eq51 eq51
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq111 eq80


@[equational_result]
theorem Equation34024_implies_Equation2 (G : Type*) [Magma G] (h : Equation34024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X0 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq176 eq49


@[equational_result]
theorem Equation34025_implies_Equation2 (G : Type*) [Magma G] (h : Equation34025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq9 eq9
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq146 eq35


@[equational_result]
theorem Equation34026_implies_Equation2 (G : Type*) [Magma G] (h : Equation34026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X0 ◇ X1) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation34029_implies_Equation2 (G : Type*) [Magma G] (h : Equation34029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34032_implies_Equation2 (G : Type*) [Magma G] (h : Equation34032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq28 eq17


@[equational_result]
theorem Equation34034_implies_Equation2 (G : Type*) [Magma G] (h : Equation34034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X2 ◇ X2) ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) := superpose eq9 eq7
  have eq39 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X0) ◇ X2) := superpose eq24 eq29
  have eq49 (X0 X1 X2 X3 X4 : G) : ((((((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)))) ◇ (X4 ◇ X4)) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)))) = X2 := superpose eq9 eq10
  have eq65 (X0 X2 X4 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ X0)) = X2 := superpose eq24 eq49
  have eq93 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq39 eq7
  have eq130 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ X0)) = X2 := superpose eq93 eq65
  have eq157 (X0 X3 : G) : X0 = X3 := superpose eq130 eq130
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq166 eq157


@[equational_result]
theorem Equation34036_implies_Equation2 (G : Type*) [Magma G] (h : Equation34036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34039_implies_Equation2 (G : Type*) [Magma G] (h : Equation34039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq30 eq19


@[equational_result]
theorem Equation34041_implies_Equation2 (G : Type*) [Magma G] (h : Equation34041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation34042_implies_Equation2 (G : Type*) [Magma G] (h : Equation34042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34044_implies_Equation2 (G : Type*) [Magma G] (h : Equation34044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34045_implies_Equation2 (G : Type*) [Magma G] (h : Equation34045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34046_implies_Equation2 (G : Type*) [Magma G] (h : Equation34046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34048_implies_Equation2 (G : Type*) [Magma G] (h : Equation34048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation34050_implies_Equation2 (G : Type*) [Magma G] (h : Equation34050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34052_implies_Equation2 (G : Type*) [Magma G] (h : Equation34052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34053_implies_Equation2 (G : Type*) [Magma G] (h : Equation34053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34054_implies_Equation2 (G : Type*) [Magma G] (h : Equation34054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34056_implies_Equation2 (G : Type*) [Magma G] (h : Equation34056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34057_implies_Equation2 (G : Type*) [Magma G] (h : Equation34057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34058_implies_Equation2 (G : Type*) [Magma G] (h : Equation34058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34060_implies_Equation2 (G : Type*) [Magma G] (h : Equation34060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34061_implies_Equation2 (G : Type*) [Magma G] (h : Equation34061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34062_implies_Equation2 (G : Type*) [Magma G] (h : Equation34062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34063_implies_Equation2 (G : Type*) [Magma G] (h : Equation34063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34065_implies_Equation2 (G : Type*) [Magma G] (h : Equation34065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq32 eq15


@[equational_result]
theorem Equation34066_implies_Equation2 (G : Type*) [Magma G] (h : Equation34066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X4 ◇ X4) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))))) = X4 := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0))) = X3 := superpose eq10 eq9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq7 eq9
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq7
  have eq31 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X4 ◇ X4) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)))))) = X4 := superpose eq10 eq17
  have eq32 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq10 eq22
  have eq33 (X0 X1 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X0) ◇ X1)))) = X4 := superpose eq32 eq31
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq10 eq28
  have eq37 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0))) = X3 := superpose eq36 eq21
  have eq41 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq37 eq33
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq10 eq41
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq82 eq44


@[equational_result]
theorem Equation34067_implies_Equation2 (G : Type*) [Magma G] (h : Equation34067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34069_implies_Equation2 (G : Type*) [Magma G] (h : Equation34069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation34071_implies_Equation2 (G : Type*) [Magma G] (h : Equation34071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq63 eq17


@[equational_result]
theorem Equation34075_implies_Equation2 (G : Type*) [Magma G] (h : Equation34075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation34077_implies_Equation2 (G : Type*) [Magma G] (h : Equation34077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation34078_implies_Equation2 (G : Type*) [Magma G] (h : Equation34078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq68 eq12


@[equational_result]
theorem Equation34079_implies_Equation2 (G : Type*) [Magma G] (h : Equation34079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation34080_implies_Equation2 (G : Type*) [Magma G] (h : Equation34080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34082_implies_Equation2 (G : Type*) [Magma G] (h : Equation34082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation34084_implies_Equation2 (G : Type*) [Magma G] (h : Equation34084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation34086_implies_Equation2 (G : Type*) [Magma G] (h : Equation34086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34087_implies_Equation2 (G : Type*) [Magma G] (h : Equation34087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34088_implies_Equation2 (G : Type*) [Magma G] (h : Equation34088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34090_implies_Equation2 (G : Type*) [Magma G] (h : Equation34090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34091_implies_Equation2 (G : Type*) [Magma G] (h : Equation34091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34092_implies_Equation2 (G : Type*) [Magma G] (h : Equation34092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34094_implies_Equation2 (G : Type*) [Magma G] (h : Equation34094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34095_implies_Equation2 (G : Type*) [Magma G] (h : Equation34095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34096_implies_Equation2 (G : Type*) [Magma G] (h : Equation34096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34097_implies_Equation2 (G : Type*) [Magma G] (h : Equation34097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34101_implies_Equation2 (G : Type*) [Magma G] (h : Equation34101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X5) = X4 := superpose eq7 eq10
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation34103_implies_Equation2 (G : Type*) [Magma G] (h : Equation34103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34104_implies_Equation2 (G : Type*) [Magma G] (h : Equation34104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34105_implies_Equation2 (G : Type*) [Magma G] (h : Equation34105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34107_implies_Equation2 (G : Type*) [Magma G] (h : Equation34107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34108_implies_Equation2 (G : Type*) [Magma G] (h : Equation34108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34109_implies_Equation2 (G : Type*) [Magma G] (h : Equation34109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34111_implies_Equation2 (G : Type*) [Magma G] (h : Equation34111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34112_implies_Equation2 (G : Type*) [Magma G] (h : Equation34112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34113_implies_Equation2 (G : Type*) [Magma G] (h : Equation34113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34114_implies_Equation2 (G : Type*) [Magma G] (h : Equation34114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34116_implies_Equation2 (G : Type*) [Magma G] (h : Equation34116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation34117_implies_Equation2 (G : Type*) [Magma G] (h : Equation34117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34118_implies_Equation2 (G : Type*) [Magma G] (h : Equation34118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation34119_implies_Equation2 (G : Type*) [Magma G] (h : Equation34119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34121_implies_Equation2 (G : Type*) [Magma G] (h : Equation34121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34122_implies_Equation2 (G : Type*) [Magma G] (h : Equation34122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34123_implies_Equation2 (G : Type*) [Magma G] (h : Equation34123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34124_implies_Equation2 (G : Type*) [Magma G] (h : Equation34124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34126_implies_Equation2 (G : Type*) [Magma G] (h : Equation34126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34127_implies_Equation2 (G : Type*) [Magma G] (h : Equation34127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34128_implies_Equation2 (G : Type*) [Magma G] (h : Equation34128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34129_implies_Equation2 (G : Type*) [Magma G] (h : Equation34129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34131_implies_Equation2 (G : Type*) [Magma G] (h : Equation34131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34132_implies_Equation2 (G : Type*) [Magma G] (h : Equation34132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34133_implies_Equation2 (G : Type*) [Magma G] (h : Equation34133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34134_implies_Equation2 (G : Type*) [Magma G] (h : Equation34134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34136_implies_Equation2 (G : Type*) [Magma G] (h : Equation34136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34137_implies_Equation2 (G : Type*) [Magma G] (h : Equation34137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34138_implies_Equation2 (G : Type*) [Magma G] (h : Equation34138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34139_implies_Equation2 (G : Type*) [Magma G] (h : Equation34139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34140_implies_Equation2 (G : Type*) [Magma G] (h : Equation34140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34142_implies_Equation2 (G : Type*) [Magma G] (h : Equation34142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq29 eq14


@[equational_result]
theorem Equation34143_implies_Equation2 (G : Type*) [Magma G] (h : Equation34143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq39 eq13


@[equational_result]
theorem Equation34144_implies_Equation2 (G : Type*) [Magma G] (h : Equation34144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation34146_implies_Equation2 (G : Type*) [Magma G] (h : Equation34146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq9 eq10
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq29 eq29
  have eq112 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq7 eq78
  have eq264 (X0 X3 : G) : X0 = X3 := superpose eq7 eq112
  have eq461 (X0 : G) : sK0 ≠ X0 := superpose eq264 eq8
  subsumption eq461 eq264


@[equational_result]
theorem Equation34148_implies_Equation2 (G : Type*) [Magma G] (h : Equation34148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq74 eq14


@[equational_result]
theorem Equation34150_implies_Equation2 (G : Type*) [Magma G] (h : Equation34150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X1))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X3)) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq11 eq7
  have eq31 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq11
  have eq44 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose eq31 eq11
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq7 eq10
  have eq122 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq76 eq76
  have eq126 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq76 eq7
  have eq181 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X3)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq126 eq9
  have eq228 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X3)) ◇ ((((X3 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X5) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2))) = X4 := superpose eq10 eq15
  have eq232 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq11 eq15
  have eq280 (X0 X1 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) = X0 := superpose eq31 eq232
  have eq281 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9 eq232
  have eq306 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq281 eq44
  have eq328 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq232 eq306
  have eq330 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq328 eq122
  have eq342 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq330
  have eq347 (X0 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq342 eq76
  have eq401 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq347 eq181
  have eq423 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq401 eq280
  have eq426 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X3)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2))) = X4 := superpose eq423 eq228
  have eq563 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2)) = X4 := superpose eq423 eq426
  have eq564 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X3)) ◇ X2) = X4 := superpose eq423 eq563
  have eq565 (X2 X3 X4 : G) : ((X4 ◇ X3) ◇ X2) = X4 := superpose eq423 eq564
  have eq566 (X2 X3 X4 : G) : (X3 ◇ X2) = X4 := superpose eq423 eq565
  have eq575 (X0 X3 : G) : X0 = X3 := superpose eq566 eq566
  have eq586 (X0 : G) : sK0 ≠ X0 := superpose eq575 eq8
  subsumption eq586 eq575


@[equational_result]
theorem Equation34151_implies_Equation2 (G : Type*) [Magma G] (h : Equation34151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq105 eq32


@[equational_result]
theorem Equation34152_implies_Equation2 (G : Type*) [Magma G] (h : Equation34152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation34154_implies_Equation2 (G : Type*) [Magma G] (h : Equation34154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq42 eq17


@[equational_result]
theorem Equation34155_implies_Equation2 (G : Type*) [Magma G] (h : Equation34155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X4))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation34156_implies_Equation2 (G : Type*) [Magma G] (h : Equation34156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation34157_implies_Equation2 (G : Type*) [Magma G] (h : Equation34157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation34159_implies_Equation2 (G : Type*) [Magma G] (h : Equation34159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq9 eq7
  have eq36 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq7 eq17
  have eq121 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq233 eq121


@[equational_result]
theorem Equation34160_implies_Equation2 (G : Type*) [Magma G] (h : Equation34160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq7 eq16
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := superpose eq16 eq10
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := superpose eq36 eq43
  have eq57 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X1 := superpose eq56 eq36
  have eq58 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq57 eq7
  have eq86 (X0 X2 : G) : X0 = X2 := superpose eq58 eq58
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq92 eq86


@[equational_result]
theorem Equation34161_implies_Equation2 (G : Type*) [Magma G] (h : Equation34161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation34163_implies_Equation2 (G : Type*) [Magma G] (h : Equation34163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq50 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq10 eq9
  have eq123 (X0 X2 : G) : X0 = X2 := superpose eq7 eq50
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq163 eq123


@[equational_result]
theorem Equation34165_implies_Equation2 (G : Type*) [Magma G] (h : Equation34165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation34167_implies_Equation2 (G : Type*) [Magma G] (h : Equation34167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq7
  have eq51 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq14
  have eq70 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X1 ◇ X0)) = X3 := superpose eq10 eq51
  have eq75 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq10 eq33
  have eq78 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) = X3 := superpose eq7 eq33
  have eq92 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = X0 := superpose eq70 eq75
  have eq108 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq92 eq78
  have eq109 (X0 X3 : G) : X0 = X3 := superpose eq7 eq108
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq215 eq109


@[equational_result]
theorem Equation34168_implies_Equation2 (G : Type*) [Magma G] (h : Equation34168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq9 eq9
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq110 eq33


@[equational_result]
theorem Equation34169_implies_Equation2 (G : Type*) [Magma G] (h : Equation34169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation34171_implies_Equation2 (G : Type*) [Magma G] (h : Equation34171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X5))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq64 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ X3) := superpose eq9 eq7
  have eq76 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq64
  have eq191 (X0 X4 : G) : X0 = X4 := superpose eq7 eq76
  have eq362 (X0 : G) : sK0 ≠ X0 := superpose eq191 eq8
  subsumption eq362 eq191


@[equational_result]
theorem Equation34172_implies_Equation2 (G : Type*) [Magma G] (h : Equation34172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X5))) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X3) = X1 := superpose eq7 eq9
  have eq55 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq19
  have eq157 (X0 X4 : G) : X0 = X4 := superpose eq7 eq55
  have eq282 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq282 eq157


@[equational_result]
theorem Equation34173_implies_Equation2 (G : Type*) [Magma G] (h : Equation34173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation34174_implies_Equation2 (G : Type*) [Magma G] (h : Equation34174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation34177_implies_Equation2 (G : Type*) [Magma G] (h : Equation34177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq99 eq29


@[equational_result]
theorem Equation34178_implies_Equation2 (G : Type*) [Magma G] (h : Equation34178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34182_implies_Equation2 (G : Type*) [Magma G] (h : Equation34182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq73 eq13


@[equational_result]
theorem Equation34184_implies_Equation2 (G : Type*) [Magma G] (h : Equation34184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq45 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ X4) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4))) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq47 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq10
  have eq72 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq47 eq45
  have eq90 (X0 X1 : G) : X0 = X1 := superpose eq7 eq72
  have eq228 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq228 eq90


@[equational_result]
theorem Equation34185_implies_Equation2 (G : Type*) [Magma G] (h : Equation34185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X2 ◇ X2))) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq161 eq51


@[equational_result]
theorem Equation34186_implies_Equation2 (G : Type*) [Magma G] (h : Equation34186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34188_implies_Equation2 (G : Type*) [Magma G] (h : Equation34188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X6)) ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X4 ◇ X5))))) = X2 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq12 eq12
  have eq26 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq18 eq13
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq26
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq153 eq49


@[equational_result]
theorem Equation34189_implies_Equation2 (G : Type*) [Magma G] (h : Equation34189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X2 ◇ X5))) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq166 eq67


@[equational_result]
theorem Equation34190_implies_Equation2 (G : Type*) [Magma G] (h : Equation34190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X3 ◇ X5))) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X4)))) ◇ (X5 ◇ X0)) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq9
  have eq21 (X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X4) = X5 := superpose eq12 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation34191_implies_Equation2 (G : Type*) [Magma G] (h : Equation34191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation34193_implies_Equation2 (G : Type*) [Magma G] (h : Equation34193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation34194_implies_Equation2 (G : Type*) [Magma G] (h : Equation34194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation34195_implies_Equation2 (G : Type*) [Magma G] (h : Equation34195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation34196_implies_Equation2 (G : Type*) [Magma G] (h : Equation34196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34198_implies_Equation2 (G : Type*) [Magma G] (h : Equation34198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X1) ◇ X4) ◇ (X0 ◇ (X5 ◇ (X3 ◇ X1)))) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq10
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X2)))) ◇ X5) ◇ (X6 ◇ (X7 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X2))))))) = ((X0 ◇ X6) ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X2)))) := superpose eq7 eq11
  have eq71 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X2)))) ◇ X5) ◇ (X6 ◇ (X7 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X2))))))) = X2 := superpose eq16 eq39
  have eq72 (X2 X5 X6 X7 : G) : ((X2 ◇ X5) ◇ (X6 ◇ (X7 ◇ X2))) = X2 := superpose eq16 eq71
  have eq74 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq72 eq7
  have eq106 (X0 X2 : G) : X0 = X2 := superpose eq74 eq74
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq108 eq106


@[equational_result]
theorem Equation34199_implies_Equation2 (G : Type*) [Magma G] (h : Equation34199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X2 := superpose eq10 eq10
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq165 eq50


@[equational_result]
theorem Equation34200_implies_Equation2 (G : Type*) [Magma G] (h : Equation34200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq59 eq13


@[equational_result]
theorem Equation34201_implies_Equation2 (G : Type*) [Magma G] (h : Equation34201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34203_implies_Equation2 (G : Type*) [Magma G] (h : Equation34203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq39 (X0 X1 X5 X6 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X1) = X5 := superpose eq12 eq10
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq39 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq114 eq47


@[equational_result]
theorem Equation34204_implies_Equation2 (G : Type*) [Magma G] (h : Equation34204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X2))) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq9
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq148 eq37


@[equational_result]
theorem Equation34205_implies_Equation2 (G : Type*) [Magma G] (h : Equation34205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X3))) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq174 eq47


@[equational_result]
theorem Equation34206_implies_Equation2 (G : Type*) [Magma G] (h : Equation34206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34208_implies_Equation2 (G : Type*) [Magma G] (h : Equation34208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation34209_implies_Equation2 (G : Type*) [Magma G] (h : Equation34209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ X4))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation34210_implies_Equation2 (G : Type*) [Magma G] (h : Equation34210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation34211_implies_Equation2 (G : Type*) [Magma G] (h : Equation34211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34213_implies_Equation2 (G : Type*) [Magma G] (h : Equation34213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq43 eq32


@[equational_result]
theorem Equation34214_implies_Equation2 (G : Type*) [Magma G] (h : Equation34214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 X6 : G) : (X0 ◇ (X0 ◇ (X5 ◇ X6))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation34215_implies_Equation2 (G : Type*) [Magma G] (h : Equation34215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34216_implies_Equation2 (G : Type*) [Magma G] (h : Equation34216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34217_implies_Equation2 (G : Type*) [Magma G] (h : Equation34217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X8 : G) : (X0 ◇ X8) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34219_implies_Equation2 (G : Type*) [Magma G] (h : Equation34219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2))))) = X1 := superpose eq7 eq10
  have eq46 (X0 X1 : G) : X0 = X1 := superpose eq7 eq19
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq103 eq46


@[equational_result]
theorem Equation34220_implies_Equation2 (G : Type*) [Magma G] (h : Equation34220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (((((((((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ X2) ◇ (X4 ◇ X4)) ◇ X0) ◇ X5) ◇ X3) ◇ X5) = X4 := superpose eq10 eq10
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((((((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X1 ◇ X1)) ◇ X3) ◇ X4) ◇ X0) ◇ (X5 ◇ X5))) ◇ X4) = X5 := superpose eq10 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq16 eq16
  have eq54 (X1 X4 X5 : G) : ((X1 ◇ X5) ◇ X4) = X5 := superpose eq34 eq31
  have eq57 (X0 X3 X4 X5 : G) : ((((X4 ◇ X0) ◇ X5) ◇ X3) ◇ X5) = X4 := superpose eq34 eq25
  have eq74 (X4 X5 : G) : (X5 ◇ X5) = X4 := superpose eq54 eq57
  have eq79 (X0 X1 : G) : X0 = X1 := superpose eq16 eq74
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq88 eq79


@[equational_result]
theorem Equation34221_implies_Equation2 (G : Type*) [Magma G] (h : Equation34221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34223_implies_Equation2 (G : Type*) [Magma G] (h : Equation34223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) = (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq7 eq10
  have eq30 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = ((((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq10 eq7
  have eq76 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0))) = X0 := superpose eq10 eq26
  have eq92 (X0 X2 X4 : G) : (X0 ◇ X4) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq76 eq30
  have eq110 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq92 eq92
  have eq145 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) = X0 := superpose eq7 eq110
  have eq226 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := superpose eq145 eq9
  have eq285 (X0 X4 : G) : X0 = X4 := superpose eq226 eq226
  have eq329 (X0 : G) : sK0 ≠ X0 := superpose eq285 eq8
  subsumption eq329 eq285


@[equational_result]
theorem Equation34225_implies_Equation2 (G : Type*) [Magma G] (h : Equation34225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34229_implies_Equation2 (G : Type*) [Magma G] (h : Equation34229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation34231_implies_Equation2 (G : Type*) [Magma G] (h : Equation34231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X0 ◇ X5))) = (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ X4) ◇ (X3 ◇ ((X2 ◇ X5) ◇ X6))) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X7) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := superpose eq7 eq10
  have eq34 (X0 X1 X2 X3 X4 X6 X7 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X6 ◇ X7))) ◇ (X3 ◇ X4)) = X6 := superpose eq10 eq7
  have eq39 (X0 X1 X2 X7 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X7) = X2 := superpose eq29 eq28
  have eq45 (X2 X3 X4 X6 : G) : (X2 ◇ (X3 ◇ X4)) = X6 := superpose eq39 eq34
  have eq85 (X0 X5 : G) : X0 = X5 := superpose eq7 eq45
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq191 eq85


@[equational_result]
theorem Equation34232_implies_Equation2 (G : Type*) [Magma G] (h : Equation34232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X5))) ◇ X2) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X0 ◇ X5))) = (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) := superpose eq7 eq7
  have eq49 (X0 X1 X2 X3 X4 X5 X6 X8 : G) : ((X3 ◇ X4) ◇ (X3 ◇ ((X2 ◇ X5) ◇ X6))) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ X8) := superpose eq10 eq10
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := superpose eq7 eq10
  have eq52 (X0 X1 X2 X4 X6 X7 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ (X6 ◇ X7))) ◇ X4) = X6 := superpose eq10 eq9
  have eq72 (X0 X1 X2 X8 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ X8) = X2 := superpose eq50 eq49
  have eq77 (X2 X4 X6 : G) : ((X2 ◇ X2) ◇ X4) = X6 := superpose eq72 eq52
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq7 eq77
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq188 eq89


@[equational_result]
theorem Equation34233_implies_Equation2 (G : Type*) [Magma G] (h : Equation34233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation34234_implies_Equation2 (G : Type*) [Magma G] (h : Equation34234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34236_implies_Equation2 (G : Type*) [Magma G] (h : Equation34236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq10
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq11
  have eq72 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq30 eq7
  have eq74 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq30 eq7
  have eq114 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq72
  have eq133 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq114 eq74
  have eq136 (X0 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq133 eq19
  have eq159 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq136
  have eq184 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq159 eq133
  have eq226 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq184 eq159
  have eq258 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq226 eq10
  have eq381 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq226 eq258
  have eq382 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq226 eq381
  have eq383 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq226 eq382
  have eq384 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq226 eq383
  have eq613 (X0 X2 : G) : X0 = X2 := superpose eq384 eq384
  have eq615 (X0 : G) : sK0 ≠ X0 := superpose eq613 eq8
  subsumption eq615 eq613


@[equational_result]
theorem Equation34238_implies_Equation2 (G : Type*) [Magma G] (h : Equation34238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq52 eq17


@[equational_result]
theorem Equation34240_implies_Equation2 (G : Type*) [Magma G] (h : Equation34240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34241_implies_Equation2 (G : Type*) [Magma G] (h : Equation34241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34242_implies_Equation2 (G : Type*) [Magma G] (h : Equation34242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34244_implies_Equation2 (G : Type*) [Magma G] (h : Equation34244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34245_implies_Equation2 (G : Type*) [Magma G] (h : Equation34245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34246_implies_Equation2 (G : Type*) [Magma G] (h : Equation34246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34248_implies_Equation2 (G : Type*) [Magma G] (h : Equation34248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34249_implies_Equation2 (G : Type*) [Magma G] (h : Equation34249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34250_implies_Equation2 (G : Type*) [Magma G] (h : Equation34250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34251_implies_Equation2 (G : Type*) [Magma G] (h : Equation34251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34255_implies_Equation2 (G : Type*) [Magma G] (h : Equation34255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation34257_implies_Equation2 (G : Type*) [Magma G] (h : Equation34257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34258_implies_Equation2 (G : Type*) [Magma G] (h : Equation34258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34259_implies_Equation2 (G : Type*) [Magma G] (h : Equation34259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34261_implies_Equation2 (G : Type*) [Magma G] (h : Equation34261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34262_implies_Equation2 (G : Type*) [Magma G] (h : Equation34262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34263_implies_Equation2 (G : Type*) [Magma G] (h : Equation34263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34265_implies_Equation2 (G : Type*) [Magma G] (h : Equation34265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34266_implies_Equation2 (G : Type*) [Magma G] (h : Equation34266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34267_implies_Equation2 (G : Type*) [Magma G] (h : Equation34267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34268_implies_Equation2 (G : Type*) [Magma G] (h : Equation34268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34270_implies_Equation2 (G : Type*) [Magma G] (h : Equation34270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation34271_implies_Equation2 (G : Type*) [Magma G] (h : Equation34271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation34272_implies_Equation2 (G : Type*) [Magma G] (h : Equation34272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation34273_implies_Equation2 (G : Type*) [Magma G] (h : Equation34273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation34275_implies_Equation2 (G : Type*) [Magma G] (h : Equation34275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34276_implies_Equation2 (G : Type*) [Magma G] (h : Equation34276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34277_implies_Equation2 (G : Type*) [Magma G] (h : Equation34277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34278_implies_Equation2 (G : Type*) [Magma G] (h : Equation34278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34280_implies_Equation2 (G : Type*) [Magma G] (h : Equation34280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34281_implies_Equation2 (G : Type*) [Magma G] (h : Equation34281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34282_implies_Equation2 (G : Type*) [Magma G] (h : Equation34282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34283_implies_Equation2 (G : Type*) [Magma G] (h : Equation34283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34285_implies_Equation2 (G : Type*) [Magma G] (h : Equation34285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34286_implies_Equation2 (G : Type*) [Magma G] (h : Equation34286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34287_implies_Equation2 (G : Type*) [Magma G] (h : Equation34287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34288_implies_Equation2 (G : Type*) [Magma G] (h : Equation34288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34290_implies_Equation2 (G : Type*) [Magma G] (h : Equation34290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34291_implies_Equation2 (G : Type*) [Magma G] (h : Equation34291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34292_implies_Equation2 (G : Type*) [Magma G] (h : Equation34292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34293_implies_Equation2 (G : Type*) [Magma G] (h : Equation34293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34294_implies_Equation2 (G : Type*) [Magma G] (h : Equation34294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34297_implies_Equation2 (G : Type*) [Magma G] (h : Equation34297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq100 eq29


@[equational_result]
theorem Equation34298_implies_Equation2 (G : Type*) [Magma G] (h : Equation34298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34302_implies_Equation2 (G : Type*) [Magma G] (h : Equation34302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq71 eq13


@[equational_result]
theorem Equation34305_implies_Equation2 (G : Type*) [Magma G] (h : Equation34305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq165 eq52


@[equational_result]
theorem Equation34306_implies_Equation2 (G : Type*) [Magma G] (h : Equation34306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34308_implies_Equation2 (G : Type*) [Magma G] (h : Equation34308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X4 ◇ X5))) ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X4 ◇ (X0 ◇ X5)))) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq21 (X0 X1 X3 : G) : (X1 ◇ X3) = (X1 ◇ X0) := superpose eq7 eq12
  have eq54 (X0 X1 X2 X3 X6 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X6) = X0 := superpose eq9 eq21
  have eq109 (X1 X2 X4 : G) : (X4 ◇ X1) = X2 := superpose eq54 eq11
  have eq114 (X0 X4 : G) : X0 = X4 := superpose eq7 eq109
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq163 eq114


@[equational_result]
theorem Equation34309_implies_Equation2 (G : Type*) [Magma G] (h : Equation34309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X2 ◇ (X4 ◇ X5))) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq163 eq61


@[equational_result]
theorem Equation34310_implies_Equation2 (G : Type*) [Magma G] (h : Equation34310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq169 eq65


@[equational_result]
theorem Equation34311_implies_Equation2 (G : Type*) [Magma G] (h : Equation34311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X6))) ◇ X7) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 X7 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X4)))) ◇ X0) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X3 X5 X7 : G) : (X3 ◇ X7) = X5 := superpose eq9 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation34315_implies_Equation2 (G : Type*) [Magma G] (h : Equation34315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation34317_implies_Equation2 (G : Type*) [Magma G] (h : Equation34317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34318_implies_Equation2 (G : Type*) [Magma G] (h : Equation34318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34319_implies_Equation2 (G : Type*) [Magma G] (h : Equation34319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34321_implies_Equation2 (G : Type*) [Magma G] (h : Equation34321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34322_implies_Equation2 (G : Type*) [Magma G] (h : Equation34322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34323_implies_Equation2 (G : Type*) [Magma G] (h : Equation34323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34325_implies_Equation2 (G : Type*) [Magma G] (h : Equation34325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34326_implies_Equation2 (G : Type*) [Magma G] (h : Equation34326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34327_implies_Equation2 (G : Type*) [Magma G] (h : Equation34327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34328_implies_Equation2 (G : Type*) [Magma G] (h : Equation34328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34331_implies_Equation2 (G : Type*) [Magma G] (h : Equation34331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq102 eq31


@[equational_result]
theorem Equation34332_implies_Equation2 (G : Type*) [Magma G] (h : Equation34332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation34334_implies_Equation2 (G : Type*) [Magma G] (h : Equation34334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34335_implies_Equation2 (G : Type*) [Magma G] (h : Equation34335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34336_implies_Equation2 (G : Type*) [Magma G] (h : Equation34336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34338_implies_Equation2 (G : Type*) [Magma G] (h : Equation34338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34339_implies_Equation2 (G : Type*) [Magma G] (h : Equation34339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34340_implies_Equation2 (G : Type*) [Magma G] (h : Equation34340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34342_implies_Equation2 (G : Type*) [Magma G] (h : Equation34342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34343_implies_Equation2 (G : Type*) [Magma G] (h : Equation34343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34344_implies_Equation2 (G : Type*) [Magma G] (h : Equation34344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34345_implies_Equation2 (G : Type*) [Magma G] (h : Equation34345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34347_implies_Equation2 (G : Type*) [Magma G] (h : Equation34347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation34348_implies_Equation2 (G : Type*) [Magma G] (h : Equation34348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation34349_implies_Equation2 (G : Type*) [Magma G] (h : Equation34349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq9
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq141 eq44


@[equational_result]
theorem Equation34350_implies_Equation2 (G : Type*) [Magma G] (h : Equation34350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation34352_implies_Equation2 (G : Type*) [Magma G] (h : Equation34352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34353_implies_Equation2 (G : Type*) [Magma G] (h : Equation34353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34354_implies_Equation2 (G : Type*) [Magma G] (h : Equation34354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34355_implies_Equation2 (G : Type*) [Magma G] (h : Equation34355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34357_implies_Equation2 (G : Type*) [Magma G] (h : Equation34357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34358_implies_Equation2 (G : Type*) [Magma G] (h : Equation34358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34359_implies_Equation2 (G : Type*) [Magma G] (h : Equation34359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34360_implies_Equation2 (G : Type*) [Magma G] (h : Equation34360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34362_implies_Equation2 (G : Type*) [Magma G] (h : Equation34362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34363_implies_Equation2 (G : Type*) [Magma G] (h : Equation34363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34364_implies_Equation2 (G : Type*) [Magma G] (h : Equation34364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34365_implies_Equation2 (G : Type*) [Magma G] (h : Equation34365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34367_implies_Equation2 (G : Type*) [Magma G] (h : Equation34367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34368_implies_Equation2 (G : Type*) [Magma G] (h : Equation34368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34369_implies_Equation2 (G : Type*) [Magma G] (h : Equation34369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34370_implies_Equation2 (G : Type*) [Magma G] (h : Equation34370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34371_implies_Equation2 (G : Type*) [Magma G] (h : Equation34371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34373_implies_Equation2 (G : Type*) [Magma G] (h : Equation34373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation34374_implies_Equation2 (G : Type*) [Magma G] (h : Equation34374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation34375_implies_Equation2 (G : Type*) [Magma G] (h : Equation34375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation34376_implies_Equation2 (G : Type*) [Magma G] (h : Equation34376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34378_implies_Equation2 (G : Type*) [Magma G] (h : Equation34378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation34379_implies_Equation2 (G : Type*) [Magma G] (h : Equation34379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation34380_implies_Equation2 (G : Type*) [Magma G] (h : Equation34380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq59 eq13


@[equational_result]
theorem Equation34381_implies_Equation2 (G : Type*) [Magma G] (h : Equation34381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34383_implies_Equation2 (G : Type*) [Magma G] (h : Equation34383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation34384_implies_Equation2 (G : Type*) [Magma G] (h : Equation34384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation34385_implies_Equation2 (G : Type*) [Magma G] (h : Equation34385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X5 ◇ X3))) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq9
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq164 eq64


@[equational_result]
theorem Equation34386_implies_Equation2 (G : Type*) [Magma G] (h : Equation34386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34388_implies_Equation2 (G : Type*) [Magma G] (h : Equation34388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq47 eq17


@[equational_result]
theorem Equation34389_implies_Equation2 (G : Type*) [Magma G] (h : Equation34389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X4))) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation34390_implies_Equation2 (G : Type*) [Magma G] (h : Equation34390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation34391_implies_Equation2 (G : Type*) [Magma G] (h : Equation34391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34393_implies_Equation2 (G : Type*) [Magma G] (h : Equation34393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation34394_implies_Equation2 (G : Type*) [Magma G] (h : Equation34394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation34395_implies_Equation2 (G : Type*) [Magma G] (h : Equation34395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34396_implies_Equation2 (G : Type*) [Magma G] (h : Equation34396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34397_implies_Equation2 (G : Type*) [Magma G] (h : Equation34397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X8 : G) : (X0 ◇ X8) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34399_implies_Equation2 (G : Type*) [Magma G] (h : Equation34399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq59 eq18


@[equational_result]
theorem Equation34400_implies_Equation2 (G : Type*) [Magma G] (h : Equation34400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq61 eq18


@[equational_result]
theorem Equation34401_implies_Equation2 (G : Type*) [Magma G] (h : Equation34401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation34402_implies_Equation2 (G : Type*) [Magma G] (h : Equation34402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation34404_implies_Equation2 (G : Type*) [Magma G] (h : Equation34404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34405_implies_Equation2 (G : Type*) [Magma G] (h : Equation34405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34406_implies_Equation2 (G : Type*) [Magma G] (h : Equation34406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34407_implies_Equation2 (G : Type*) [Magma G] (h : Equation34407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34409_implies_Equation2 (G : Type*) [Magma G] (h : Equation34409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34410_implies_Equation2 (G : Type*) [Magma G] (h : Equation34410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34411_implies_Equation2 (G : Type*) [Magma G] (h : Equation34411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34412_implies_Equation2 (G : Type*) [Magma G] (h : Equation34412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34414_implies_Equation2 (G : Type*) [Magma G] (h : Equation34414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34415_implies_Equation2 (G : Type*) [Magma G] (h : Equation34415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34416_implies_Equation2 (G : Type*) [Magma G] (h : Equation34416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34417_implies_Equation2 (G : Type*) [Magma G] (h : Equation34417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34419_implies_Equation2 (G : Type*) [Magma G] (h : Equation34419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34420_implies_Equation2 (G : Type*) [Magma G] (h : Equation34420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34421_implies_Equation2 (G : Type*) [Magma G] (h : Equation34421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34422_implies_Equation2 (G : Type*) [Magma G] (h : Equation34422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34423_implies_Equation2 (G : Type*) [Magma G] (h : Equation34423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34425_implies_Equation2 (G : Type*) [Magma G] (h : Equation34425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation34426_implies_Equation2 (G : Type*) [Magma G] (h : Equation34426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation34427_implies_Equation2 (G : Type*) [Magma G] (h : Equation34427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X3 ◇ X5))) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ X0)))) ◇ (X5 ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq9 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq47 eq39


@[equational_result]
theorem Equation34428_implies_Equation2 (G : Type*) [Magma G] (h : Equation34428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation34430_implies_Equation2 (G : Type*) [Magma G] (h : Equation34430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34431_implies_Equation2 (G : Type*) [Magma G] (h : Equation34431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34432_implies_Equation2 (G : Type*) [Magma G] (h : Equation34432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34433_implies_Equation2 (G : Type*) [Magma G] (h : Equation34433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34435_implies_Equation2 (G : Type*) [Magma G] (h : Equation34435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34436_implies_Equation2 (G : Type*) [Magma G] (h : Equation34436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34437_implies_Equation2 (G : Type*) [Magma G] (h : Equation34437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34438_implies_Equation2 (G : Type*) [Magma G] (h : Equation34438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34440_implies_Equation2 (G : Type*) [Magma G] (h : Equation34440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34441_implies_Equation2 (G : Type*) [Magma G] (h : Equation34441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34442_implies_Equation2 (G : Type*) [Magma G] (h : Equation34442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34443_implies_Equation2 (G : Type*) [Magma G] (h : Equation34443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34445_implies_Equation2 (G : Type*) [Magma G] (h : Equation34445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34446_implies_Equation2 (G : Type*) [Magma G] (h : Equation34446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34447_implies_Equation2 (G : Type*) [Magma G] (h : Equation34447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34448_implies_Equation2 (G : Type*) [Magma G] (h : Equation34448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34449_implies_Equation2 (G : Type*) [Magma G] (h : Equation34449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34451_implies_Equation2 (G : Type*) [Magma G] (h : Equation34451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation34452_implies_Equation2 (G : Type*) [Magma G] (h : Equation34452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X0))) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq57 eq18


@[equational_result]
theorem Equation34453_implies_Equation2 (G : Type*) [Magma G] (h : Equation34453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation34454_implies_Equation2 (G : Type*) [Magma G] (h : Equation34454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation34456_implies_Equation2 (G : Type*) [Magma G] (h : Equation34456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34457_implies_Equation2 (G : Type*) [Magma G] (h : Equation34457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34458_implies_Equation2 (G : Type*) [Magma G] (h : Equation34458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34459_implies_Equation2 (G : Type*) [Magma G] (h : Equation34459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34461_implies_Equation2 (G : Type*) [Magma G] (h : Equation34461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34462_implies_Equation2 (G : Type*) [Magma G] (h : Equation34462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34463_implies_Equation2 (G : Type*) [Magma G] (h : Equation34463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34464_implies_Equation2 (G : Type*) [Magma G] (h : Equation34464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34466_implies_Equation2 (G : Type*) [Magma G] (h : Equation34466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34467_implies_Equation2 (G : Type*) [Magma G] (h : Equation34467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34468_implies_Equation2 (G : Type*) [Magma G] (h : Equation34468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34469_implies_Equation2 (G : Type*) [Magma G] (h : Equation34469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34471_implies_Equation2 (G : Type*) [Magma G] (h : Equation34471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34472_implies_Equation2 (G : Type*) [Magma G] (h : Equation34472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34473_implies_Equation2 (G : Type*) [Magma G] (h : Equation34473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34474_implies_Equation2 (G : Type*) [Magma G] (h : Equation34474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34475_implies_Equation2 (G : Type*) [Magma G] (h : Equation34475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34477_implies_Equation2 (G : Type*) [Magma G] (h : Equation34477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation34478_implies_Equation2 (G : Type*) [Magma G] (h : Equation34478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X5 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation34479_implies_Equation2 (G : Type*) [Magma G] (h : Equation34479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34480_implies_Equation2 (G : Type*) [Magma G] (h : Equation34480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X5) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34481_implies_Equation2 (G : Type*) [Magma G] (h : Equation34481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X8 : G) : (X0 ◇ X8) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation34483_implies_Equation2 (G : Type*) [Magma G] (h : Equation34483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34484_implies_Equation2 (G : Type*) [Magma G] (h : Equation34484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34485_implies_Equation2 (G : Type*) [Magma G] (h : Equation34485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34486_implies_Equation2 (G : Type*) [Magma G] (h : Equation34486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34487_implies_Equation2 (G : Type*) [Magma G] (h : Equation34487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34489_implies_Equation2 (G : Type*) [Magma G] (h : Equation34489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34490_implies_Equation2 (G : Type*) [Magma G] (h : Equation34490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34491_implies_Equation2 (G : Type*) [Magma G] (h : Equation34491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34492_implies_Equation2 (G : Type*) [Magma G] (h : Equation34492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34493_implies_Equation2 (G : Type*) [Magma G] (h : Equation34493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34495_implies_Equation2 (G : Type*) [Magma G] (h : Equation34495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34496_implies_Equation2 (G : Type*) [Magma G] (h : Equation34496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34497_implies_Equation2 (G : Type*) [Magma G] (h : Equation34497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34498_implies_Equation2 (G : Type*) [Magma G] (h : Equation34498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34499_implies_Equation2 (G : Type*) [Magma G] (h : Equation34499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34501_implies_Equation2 (G : Type*) [Magma G] (h : Equation34501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34502_implies_Equation2 (G : Type*) [Magma G] (h : Equation34502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34503_implies_Equation2 (G : Type*) [Magma G] (h : Equation34503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34504_implies_Equation2 (G : Type*) [Magma G] (h : Equation34504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34505_implies_Equation2 (G : Type*) [Magma G] (h : Equation34505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34507_implies_Equation2 (G : Type*) [Magma G] (h : Equation34507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34508_implies_Equation2 (G : Type*) [Magma G] (h : Equation34508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34509_implies_Equation2 (G : Type*) [Magma G] (h : Equation34509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34510_implies_Equation2 (G : Type*) [Magma G] (h : Equation34510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34511_implies_Equation2 (G : Type*) [Magma G] (h : Equation34511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34512_implies_Equation2 (G : Type*) [Magma G] (h : Equation34512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34718_implies_Equation2 (G : Type*) [Magma G] (h : Equation34718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X3) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq13 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ X2) := superpose eq9 eq11
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X3) := superpose eq13 eq10
  have eq15 (X0 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq14
  have eq16 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq15 eq7
  have eq17 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq15
  have eq20 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq16 eq17
  have eq21 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq16 eq20
  have eq23 (X0 X1 : G) : X0 = X1 := superpose eq16 eq21
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation34721_implies_Equation2 (G : Type*) [Magma G] (h : Equation34721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) := superpose eq7 eq11
  have eq27 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq12
  have eq29 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) = X2 := superpose eq27 eq9
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq27 eq29
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation34723_implies_Equation2 (G : Type*) [Magma G] (h : Equation34723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X1) := superpose eq14 eq10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq20
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq28
  have eq33 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq14 eq7
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq14 eq9
  have eq63 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0)) := superpose eq7 eq33
  have eq65 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq20 eq33
  have eq75 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq9 eq11
  have eq89 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq75 eq63
  have eq91 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq89 eq32
  have eq92 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq89 eq45
  have eq104 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq89
  have eq147 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq89 eq104
  have eq148 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq147 eq92
  have eq157 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq147 eq65
  have eq165 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq147 eq148
  have eq166 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq91 eq165
  have eq173 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq157 eq166
  have eq190 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq173 eq7
  have eq202 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq173 eq89
  have eq252 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq173 eq202
  have eq253 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq252 eq190
  have eq276 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq252 eq253
  have eq382 (X0 X2 : G) : X0 = X2 := superpose eq276 eq276
  have eq384 (X0 : G) : sK0 ≠ X0 := superpose eq382 eq8
  subsumption eq384 eq382


@[equational_result]
theorem Equation34724_implies_Equation2 (G : Type*) [Magma G] (h : Equation34724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq69 eq23


@[equational_result]
theorem Equation34725_implies_Equation2 (G : Type*) [Magma G] (h : Equation34725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : ((X0 ◇ X0) ◇ X2) = (X0 ◇ X4) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X4) := superpose eq7 eq12
  have eq31 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq14
  have eq33 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq31 eq7
  have eq39 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq31 eq33
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation34728_implies_Equation2 (G : Type*) [Magma G] (h : Equation34728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X2) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq7 eq12
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq16 eq11
  have eq37 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq16 eq30
  have eq38 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq37 eq12
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq37 eq38
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq52 eq50


@[equational_result]
theorem Equation34731_implies_Equation2 (G : Type*) [Magma G] (h : Equation34731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ X2) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) := superpose eq7 eq12
  have eq31 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq13
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X3) = X2 := superpose eq31 eq9
  have eq43 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq31 eq34
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq63 eq44


@[equational_result]
theorem Equation34733_implies_Equation2 (G : Type*) [Magma G] (h : Equation34733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3)) = X0 := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X2))) = X0 := superpose eq9 eq9
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq21
  have eq42 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0)) = X0 := superpose eq37 eq37
  have eq43 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq37 eq9
  have eq51 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq37 eq11
  have eq52 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq37 eq7
  have eq57 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq43 eq42
  have eq58 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq43 eq37
  have eq69 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq52 eq51
  have eq100 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq57 eq10
  have eq104 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq57 eq10
  have eq106 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq57 eq7
  have eq112 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq57 eq104
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq106 eq100
  have eq132 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq57 eq58
  have eq160 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq132 eq112
  have eq164 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq132 eq120
  have eq170 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq58 eq164
  have eq171 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq160 eq170
  have eq269 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0) := superpose eq132 eq16
  have eq295 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq69 eq269
  have eq296 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq171 eq295
  have eq297 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq132 eq296
  have eq298 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq132 eq297
  have eq310 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) := superpose eq171 eq7
  have eq334 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq298 eq310
  have eq344 (X0 X1 X2 X3 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3)) = X0 := superpose eq334 eq12
  have eq449 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := superpose eq334 eq344
  have eq450 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq334 eq449
  have eq451 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq334 eq450
  have eq684 (X0 X2 : G) : X0 = X2 := superpose eq451 eq451
  have eq692 (X0 : G) : sK0 ≠ X0 := superpose eq684 eq8
  subsumption eq692 eq684


@[equational_result]
theorem Equation34735_implies_Equation2 (G : Type*) [Magma G] (h : Equation34735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X4) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X4) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X5) := superpose eq7 eq12
  have eq32 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq7 eq13
  have eq35 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X4)) ◇ X5) = X3 := superpose eq32 eq9
  have eq44 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq32 eq35
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq64 eq45


@[equational_result]
theorem Equation34737_implies_Equation2 (G : Type*) [Magma G] (h : Equation34737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X3) ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X2 := superpose eq11 eq9
  have eq31 (X0 X1 X2 X4 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X4) ◇ X2))) = X0 := superpose eq11 eq9
  have eq32 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) = X0 := superpose eq11 eq7
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq32
  have eq185 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) := superpose eq29 eq42
  have eq190 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq42
  have eq288 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq190
  have eq316 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq190 eq31
  have eq320 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq190 eq32
  have eq423 (X0 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq288 eq185
  have eq525 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq190 eq423
  have eq571 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq288 eq316
  have eq573 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := superpose eq288 eq320
  have eq574 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq573 eq525
  have eq575 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq574 eq573
  have eq588 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq575 eq571
  have eq684 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq575 eq588
  have eq685 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0))) := superpose eq575 eq684
  have eq686 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq575 eq685
  have eq757 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq686 eq7
  have eq911 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq686 eq757
  have eq1005 (X0 X2 : G) : X0 = X2 := superpose eq911 eq911
  have eq1007 (X0 : G) : sK0 ≠ X0 := superpose eq1005 eq8
  subsumption eq1007 eq1005


@[equational_result]
theorem Equation34738_implies_Equation2 (G : Type*) [Magma G] (h : Equation34738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq23 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq15 eq7
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq34 eq26


@[equational_result]
theorem Equation34739_implies_Equation2 (G : Type*) [Magma G] (h : Equation34739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X2 ◇ X0) = (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X4) := superpose eq7 eq7
  have eq12 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X0) = (X0 ◇ X4) := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq7 eq12
  have eq31 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq16 eq11
  have eq38 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq31 eq12
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq31 eq38
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq52 eq42


@[equational_result]
theorem Equation34741_implies_Equation2 (G : Type*) [Magma G] (h : Equation34741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X3) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)))) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := superpose eq7 eq11
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq11 eq7
  have eq21 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0))) = X0 := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq9 eq11
  have eq36 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq9
  have eq37 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq14 eq7
  have eq104 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq21 eq11
  have eq106 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq21 eq7
  have eq119 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq37 eq106
  have eq161 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq31 eq31
  have eq162 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq7 eq31
  have eq167 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = X0 := superpose eq31 eq9
  have eq264 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1)) = (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1))) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq12 eq106
  have eq269 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1)) := superpose eq7 eq162
  have eq273 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose eq37 eq162
  have eq274 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)))) := superpose eq12 eq162
  have eq279 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) := superpose eq31 eq162
  have eq311 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq37 eq273
  have eq315 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq311 eq119
  have eq316 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq311 eq14
  have eq317 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq311 eq36
  have eq362 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq316 eq315
  have eq363 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq311 eq362
  have eq364 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq316 eq363
  have eq365 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq311 eq364
  have eq367 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) = (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq365 eq264
  have eq385 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq365 eq104
  have eq387 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq365 eq106
  have eq423 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq365 eq317
  have eq424 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := superpose eq365 eq423
  have eq425 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq424 eq385
  have eq555 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq167 eq279
  have eq648 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq365 eq7
  have eq746 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) = (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1))) := superpose eq12 eq425
  have eq778 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) = (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) := superpose eq269 eq746
  have eq898 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1))) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq387 eq17
  have eq1209 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq162 eq555
  have eq1247 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq555 eq425
  have eq1249 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq555 eq1209
  have eq1250 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1249 eq161
  have eq1266 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq1247 eq1250
  have eq1296 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq1266 eq1249
  have eq1491 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq1266 eq1296
  have eq1496 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq1491 eq648
  have eq1519 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1496 eq1491
  have eq1520 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) := superpose eq1519 eq778
  have eq1561 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := superpose eq1520 eq12
  have eq1574 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) := superpose eq1520 eq269
  have eq1575 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)))) := superpose eq1520 eq274
  have eq1577 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq1520 eq367
  have eq1628 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = (((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq1266 eq1577
  have eq1629 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) = ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X0) := superpose eq1628 eq1575
  have eq1631 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X0) := superpose eq1574 eq1629
  have eq1632 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq1631 eq1628
  have eq1634 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X0 := superpose eq1561 eq1632
  have eq1636 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1634 eq1520
  have eq1651 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq1636 eq898
  have eq1787 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1636 eq1651
  have eq1788 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq1636 eq1787
  have eq1789 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X1 := superpose eq1636 eq1788
  have eq1790 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1636 eq1789
  have eq2743 (X0 X1 : G) : X0 = X1 := superpose eq1636 eq1790
  have eq2756 (X0 : G) : sK0 ≠ X0 := superpose eq2743 eq8
  subsumption eq2756 eq2743


@[equational_result]
theorem Equation34743_implies_Equation2 (G : Type*) [Magma G] (h : Equation34743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : ((X0 ◇ X2) ◇ X1) = (X0 ◇ X4) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X4) = (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X5) := superpose eq7 eq12
  have eq32 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq7 eq13
  have eq34 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))) ◇ X5) = X3 := superpose eq32 eq9
  have eq40 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq32 eq34
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq43 eq41


@[equational_result]
theorem Equation34745_implies_Equation2 (G : Type*) [Magma G] (h : Equation34745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X3) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3))) ◇ (X0 ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = (((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = ((X1 ◇ X0) ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ X3) ◇ X3))) := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X0 := superpose eq7 eq12
  have eq31 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq12
  have eq36 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X0))) ◇ X2) = X0 := superpose eq12 eq7
  have eq42 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq31 eq7
  have eq53 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ (((((X2 ◇ X3) ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0)) := superpose eq11 eq11
  have eq73 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) = ((((((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) ◇ X3) ◇ X3) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ (((((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) ◇ X3) ◇ X3) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0)))) := superpose eq11 eq28
  have eq115 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq9 eq10
  have eq117 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq28 eq10
  have eq133 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)))) = (((X3 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))))) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)))) ◇ X3) := superpose eq10 eq11
  have eq150 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq31 eq117
  have eq206 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X0 := superpose eq9 eq115
  have eq334 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X3)) = ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq9 eq206
  have eq385 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X3)) = (X1 ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq7 eq334
  have eq498 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X1 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X3)) := superpose eq7 eq385
  have eq499 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X1 ◇ ((((((X0 ◇ X2) ◇ X2) ◇ (((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X0)) ◇ X0) ◇ X4) ◇ X4)) := superpose eq36 eq385
  have eq556 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X2))) ◇ X3) = X0 := superpose eq385 eq36
  have eq708 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X3) = X0 := superpose eq498 eq556
  have eq903 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq708 eq11
  have eq968 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq903 eq42
  have eq975 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq903 eq150
  have eq1044 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0)) ◇ X0) := superpose eq12 eq903
  have eq1087 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq903 eq12
  have eq1088 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq903 eq206
  have eq1130 (X0 X1 X4 : G) : (X1 ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X4) ◇ X4)) := superpose eq1044 eq499
  have eq1149 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq1087 eq975
  have eq1150 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1130 eq1149
  have eq1154 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq1088 eq968
  have eq1167 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq1154 eq1087
  have eq1176 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1167 eq1150
  have eq1200 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1088 eq1176
  have eq1205 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq1200 eq903
  have eq1264 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq1200 eq1205
  have eq1266 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := superpose eq1264 eq15
  have eq1272 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X2) = ((X0 ◇ X2) ◇ (((((X2 ◇ X3) ◇ X3) ◇ X2) ◇ X0) ◇ X0)) := superpose eq1264 eq53
  have eq1282 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X2) ◇ (((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq1264 eq73
  have eq1421 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) = (((X3 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0)) ◇ X0) ◇ X3) := superpose eq1266 eq133
  have eq1431 (X0 X1 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ X3) = X1 := superpose eq7 eq1421
  have eq1438 (X0 X2 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq1264 eq1272
  have eq1445 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq1264 eq1282
  have eq1446 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq1438 eq1445
  have eq1447 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq1264 eq1446
  have eq1450 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose eq1447 eq12
  have eq1666 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq1431 eq1450
  have eq1667 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1447 eq1666
  have eq1669 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = X1 := superpose eq1667 eq1431
  have eq1673 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq1667 eq1669
  have eq2544 (X0 X1 : G) : X0 = X1 := superpose eq1667 eq1673
  have eq2554 (X0 : G) : sK0 ≠ X0 := superpose eq2544 eq8
  subsumption eq2554 eq2544


@[equational_result]
theorem Equation34746_implies_Equation2 (G : Type*) [Magma G] (h : Equation34746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq127 eq32


@[equational_result]
theorem Equation34747_implies_Equation2 (G : Type*) [Magma G] (h : Equation34747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X2) = (X0 ◇ X4) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X4) := superpose eq7 eq12
  have eq31 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq7 eq13
  have eq33 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq31 eq7
  have eq39 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq31 eq33
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation34749_implies_Equation2 (G : Type*) [Magma G] (h : Equation34749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X4) ◇ X5)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (((X4 ◇ X0) ◇ X1) ◇ X4) = X0 := superpose eq7 eq11
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X2 ◇ X0)) := superpose eq7 eq11
  have eq30 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ ((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) ◇ X1) ◇ X5) ◇ X6))) = X2 := superpose eq11 eq9
  have eq41 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X5) ◇ X6)) ◇ X0) := superpose eq7 eq9
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (((((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) ◇ X1) ◇ X5) ◇ X6) ◇ X2))) = X2 := superpose eq17 eq30
  have eq96 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) := superpose eq12 eq11
  have eq104 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq12 eq13
  have eq108 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) := superpose eq13 eq96
  have eq109 (X0 X1 X2 X5 X6 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (((X1 ◇ X0) ◇ X5) ◇ X6)) ◇ X0) := superpose eq108 eq41
  have eq114 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq104 eq109
  have eq116 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((((((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) ◇ X1) ◇ X5) ◇ X6))) = X2 := superpose eq114 eq50
  have eq156 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq114 eq116
  have eq157 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq114 eq156
  have eq166 (X0 X1 : G) : X0 = X1 := superpose eq114 eq157
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq168 eq166


@[equational_result]
theorem Equation34750_implies_Equation2 (G : Type*) [Magma G] (h : Equation34750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X2 ◇ X4) ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq131 eq42


@[equational_result]
theorem Equation34751_implies_Equation2 (G : Type*) [Magma G] (h : Equation34751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq120 eq39


@[equational_result]
theorem Equation34752_implies_Equation2 (G : Type*) [Magma G] (h : Equation34752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 X6 : G) : ((X0 ◇ X2) ◇ X3) = (X0 ◇ X6) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X5 X6 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X6) = (X0 ◇ X5) := superpose eq7 eq12
  have eq33 (X0 X5 : G) : (X0 ◇ X5) = X0 := superpose eq7 eq14
  have eq34 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X0 := superpose eq33 eq7
  have eq39 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq33 eq34
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation34755_implies_Equation2 (G : Type*) [Magma G] (h : Equation34755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq13
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq20
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq68 eq42


@[equational_result]
theorem Equation34758_implies_Equation2 (G : Type*) [Magma G] (h : Equation34758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq9 eq9
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq69 eq52


@[equational_result]
theorem Equation34760_implies_Equation2 (G : Type*) [Magma G] (h : Equation34760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) := superpose eq9 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4))) := superpose eq10 eq9
  have eq74 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X0) := superpose eq22 eq17
  have eq77 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq17
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ X2) := superpose eq9 eq17
  have eq98 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq77 eq28
  have eq101 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq77 eq7
  have eq125 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq77 eq98
  have eq126 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq77 eq125
  have eq127 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq77 eq126
  have eq128 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq77 eq127
  have eq179 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq78 eq101
  have eq192 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq179 eq128
  have eq193 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq192 eq22
  have eq228 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq193 eq74
  have eq230 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq193 eq228
  have eq232 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq230 eq193
  have eq239 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq232 eq78
  have eq254 (X0 X1 : G) : X0 = X1 := superpose eq232 eq239
  have eq267 (X0 : G) : sK0 ≠ X0 := superpose eq254 eq8
  subsumption eq267 eq254


@[equational_result]
theorem Equation34761_implies_Equation2 (G : Type*) [Magma G] (h : Equation34761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation34762_implies_Equation2 (G : Type*) [Magma G] (h : Equation34762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation34765_implies_Equation2 (G : Type*) [Magma G] (h : Equation34765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ X2) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) = X0 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq11 eq7
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0)) ◇ X3) = X0 := superpose eq11 eq7
  have eq31 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq22 eq24
  have eq32 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq31 eq23
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X0 := superpose eq32 eq19
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq32 eq33
  have eq44 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq43
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq50 eq45


@[equational_result]
theorem Equation34768_implies_Equation2 (G : Type*) [Magma G] (h : Equation34768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq9
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq70 eq54


@[equational_result]
theorem Equation34770_implies_Equation2 (G : Type*) [Magma G] (h : Equation34770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) := superpose eq9 eq7
  have eq22 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq13 eq9
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq22
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) := superpose eq30 eq13
  have eq59 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq35 eq9
  have eq68 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq7 eq59
  have eq75 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq68 eq7
  have eq106 (X0 X1 : G) : X0 = X1 := superpose eq68 eq75
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq118 eq106


@[equational_result]
theorem Equation34771_implies_Equation2 (G : Type*) [Magma G] (h : Equation34771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq10 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X3 ◇ ((((X2 ◇ X3) ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1)) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1)) = X3 := superpose eq10 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3) := superpose eq10 eq7
  have eq16 (X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) ◇ X3) = X2 := superpose eq13 eq9
  have eq20 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq10 eq16
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2))) ◇ X3)) ◇ X3) = X2 := superpose eq16 eq7
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) = (X0 ◇ X2) := superpose eq7 eq20
  have eq46 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq25 eq11
  have eq47 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq46 eq25
  have eq48 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq46 eq7
  have eq50 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = (X3 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) := superpose eq47 eq13
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ X3)) ◇ X3) = X2 := superpose eq47 eq23
  have eq54 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3) = ((X2 ◇ X0) ◇ X1) := superpose eq47 eq15
  have eq55 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq47 eq14
  have eq56 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) = (((X2 ◇ X0) ◇ X1) ◇ X3) := superpose eq47 eq12
  have eq59 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) := superpose eq47 eq54
  have eq60 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X3) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq47 eq56
  have eq61 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) = (((X2 ◇ X0) ◇ X1) ◇ X3) := superpose eq47 eq60
  have eq63 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X3)) ◇ X3) = X2 := superpose eq61 eq51
  have eq67 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq20
  have eq70 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq67 eq50
  have eq73 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) := superpose eq67 eq59
  have eq74 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq67 eq61
  have eq76 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3)) ◇ X3) = X2 := superpose eq67 eq63
  have eq78 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) := superpose eq74 eq70
  have eq83 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3))) ◇ X3) = X2 := superpose eq74 eq76
  have eq84 (X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq78 eq83
  have eq85 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq67 eq84
  have eq86 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X2 := superpose eq85 eq73
  have eq89 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X1)) = X3 := superpose eq86 eq55
  have eq94 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq86 eq89
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq94 eq94
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq115 eq101


@[equational_result]
theorem Equation34772_implies_Equation2 (G : Type*) [Magma G] (h : Equation34772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq9
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq59 eq41


@[equational_result]
theorem Equation34774_implies_Equation2 (G : Type*) [Magma G] (h : Equation34774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq9
  have eq42 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq17 eq17
  have eq51 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq17 eq7
  have eq75 (X0 X1 X2 X4 : G) : (((((X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1))) ◇ X0) ◇ X4) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X4)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1))) ◇ X0)) = X4 := superpose eq9 eq10
  have eq84 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) = (((X0 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2))) ◇ X0) := superpose eq10 eq11
  have eq109 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) = (((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq13
  have eq133 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq17 eq51
  have eq143 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X3) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) = X3 := superpose eq7 eq51
  have eq171 (X0 X1 X2 : G) : ((((((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ X2)) = X0 := superpose eq13 eq15
  have eq447 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq17 eq42
  have eq1141 (X0 X1 X2 : G) : (((((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1)) = X1 := superpose eq7 eq75
  have eq1211 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = ((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ ((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)))) ◇ (X0 ◇ ((((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) ◇ X4) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2)))) := superpose eq75 eq17
  have eq1342 (X0 X2 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq143
  have eq1419 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq84
  have eq1480 (X0 X1 X2 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq1342 eq7
  have eq1611 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq1342 eq1480
  have eq1794 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq1611 eq1611
  have eq1799 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq1611 eq51
  have eq2237 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq1342 eq1419
  have eq2238 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq1419
  have eq2250 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1419 eq42
  have eq2397 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq2238 eq15
  have eq2410 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq2397 eq2250
  have eq2591 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose eq2410 eq17
  have eq2593 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq2410 eq133
  have eq2612 (X0 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose eq2397 eq2591
  have eq2614 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ X0) := superpose eq2397 eq2593
  have eq2615 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq2612 eq2614
  have eq2616 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq2615 eq2612
  have eq2629 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq2616 eq2615
  have eq2633 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq2629 eq2237
  have eq2635 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq2629 eq2238
  have eq2655 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq2635
  have eq2656 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq2655 eq1794
  have eq2659 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq2655 eq1342
  have eq2681 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq2655 eq1799
  have eq2687 (X0 X1 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq2655 eq2633
  have eq2692 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq2655 eq2656
  have eq2702 (X0 X1 X2 : G) : ((((X2 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := superpose eq2659 eq171
  have eq2786 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq2659 eq11
  have eq3255 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq2655 eq2702
  have eq3256 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X0 := superpose eq2659 eq3255
  have eq3257 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq2655 eq3256
  have eq3263 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq2655 eq2786
  have eq3326 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq2659 eq2687
  have eq3327 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq3263 eq3326
  have eq3338 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = ((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ ((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0))) ◇ (X0 ◇ ((((((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) ◇ X4) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2)))) := superpose eq3327 eq1211
  have eq3346 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq3327 eq447
  have eq3406 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq3327 eq2681
  have eq3408 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq3327 eq2692
  have eq3443 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq3327 eq3346
  have eq3444 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq3327 eq3443
  have eq3456 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq3327 eq3406
  have eq3457 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq3327 eq3456
  have eq3458 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq3457 eq3408
  have eq3459 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq3458 eq3444
  have eq3460 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq2655 eq3459
  have eq3461 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq2659 eq3460
  have eq3462 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1)) = X1 := superpose eq3461 eq1141
  have eq3472 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1)) = X1 := superpose eq2659 eq3462
  have eq3473 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq3472 eq109
  have eq3489 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) := superpose eq3327 eq3473
  have eq3604 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) = ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0))) ◇ (X0 ◇ ((((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) ◇ X4) ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))))) := superpose eq3489 eq3338
  have eq3619 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) ◇ (X0 ◇ (((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ X4) ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))))) := superpose eq2655 eq3604
  have eq3620 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq3257 eq3619
  have eq3621 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) ◇ X0) := superpose eq2655 eq3620
  have eq3622 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = ((((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ X0) := superpose eq3327 eq3621
  have eq3623 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = (((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) := superpose eq3461 eq3622
  have eq3643 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq3623 eq9
  have eq4103 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq3643
  have eq4104 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq2655 eq4103
  have eq4106 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ X1) := superpose eq4104 eq3489
  have eq4109 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq2655 eq4106
  have eq4112 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq4109 eq7
  have eq4180 (X0 X2 : G) : X0 = X2 := superpose eq4112 eq4112
  have eq4182 (X0 : G) : sK0 ≠ X0 := superpose eq4180 eq8
  subsumption eq4182 eq4180


@[equational_result]
theorem Equation34776_implies_Equation2 (G : Type*) [Magma G] (h : Equation34776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ X4) := superpose eq7 eq7
  have eq18 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq114 eq51


@[equational_result]
theorem Equation34780_implies_Equation2 (G : Type*) [Magma G] (h : Equation34780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ X4) := superpose eq7 eq7
  have eq18 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq158 eq53


@[equational_result]
theorem Equation34782_implies_Equation2 (G : Type*) [Magma G] (h : Equation34782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ ((X1 ◇ X3) ◇ X3)) ◇ X4) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ ((X1 ◇ X3) ◇ X3))) = X4 := superpose eq7 eq10
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq10
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq10
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq11 eq52
  have eq57 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) ◇ X3) = ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ X1))) := superpose eq7 eq22
  have eq67 (X0 X1 X2 X4 : G) : (X0 ◇ X0) = ((X2 ◇ (((((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ X4) ◇ X4)) ◇ (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq22 eq9
  have eq115 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq54 eq54
  have eq117 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq22 eq54
  have eq139 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq54 eq10
  have eq175 (X0 X2 X4 : G) : (X0 ◇ X0) = ((X2 ◇ (((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X4) ◇ X4)) ◇ (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq117 eq67
  have eq239 (X0 X1 X2 X3 X4 X5 : G) : ((((((X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3))) ◇ ((X1 ◇ X4) ◇ X4)) ◇ X0) ◇ X2) ◇ (X5 ◇ ((((X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3))) ◇ ((X1 ◇ X4) ◇ X4)) ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3))) ◇ ((X1 ◇ X4) ◇ X4)))) = X5 := superpose eq19 eq54
  have eq261 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq115
  have eq263 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq54 eq115
  have eq264 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq115 eq115
  have eq271 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq22 eq115
  have eq272 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq115 eq7
  have eq293 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq115 eq54
  have eq294 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq115 eq10
  have eq297 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq261 eq139
  have eq303 (X0 X2 X4 : G) : (X0 ◇ X0) = ((X2 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X4) ◇ X4)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq264 eq175
  have eq310 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ X2) := superpose eq271 eq22
  have eq339 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ X1))) := superpose eq310 eq57
  have eq395 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq261 eq294
  have eq437 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq54 eq272
  have eq444 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq310 eq272
  have eq469 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq444 eq263
  have eq472 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq444 eq339
  have eq478 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq444 eq395
  have eq491 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq444 eq261
  have eq500 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) = X2 := superpose eq444 eq293
  have eq502 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq444 eq297
  have eq504 (X0 X2 X4 : G) : ((X2 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X4) ◇ X4)) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq444 eq303
  have eq550 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq444 eq478
  have eq606 (X0 X1 X2 X4 X5 : G) : ((((((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X4) ◇ X4)) ◇ X0) ◇ X2) ◇ (X5 ◇ ((((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X4) ◇ X4)) ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X4) ◇ X4)))) = X5 := superpose eq491 eq239
  have eq614 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq491 eq472
  have eq669 (X0 X1 X2 X5 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) = X5 := superpose eq54 eq606
  have eq692 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X2) := superpose eq550 eq502
  have eq738 (X0 X2 : G) : ((X2 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq692 eq504
  have eq739 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X1 := superpose eq738 eq437
  have eq747 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq739 eq469
  have eq770 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq747 eq614
  have eq786 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq739 eq770
  have eq787 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq739 eq786
  have eq788 (X0 X1 X2 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = X5 := superpose eq787 eq669
  have eq789 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq787 eq500
  have eq820 (X0 X5 : G) : (X5 ◇ X0) = X5 := superpose eq789 eq788
  have eq827 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq820 eq787
  have eq868 (X0 X1 : G) : X0 = X1 := superpose eq827 eq820
  have eq878 (X0 : G) : sK0 ≠ X0 := superpose eq868 eq8
  subsumption eq878 eq868


@[equational_result]
theorem Equation34784_implies_Equation2 (G : Type*) [Magma G] (h : Equation34784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq9
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq64 eq43


@[equational_result]
theorem Equation34786_implies_Equation2 (G : Type*) [Magma G] (h : Equation34786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X5)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ (X0 ◇ X5)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (((X0 ◇ X4) ◇ X1) ◇ X0) = X4 := superpose eq7 eq11
  have eq56 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X5) := superpose eq9 eq16
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq56 eq10
  have eq93 (X0 X5 : G) : X0 = X5 := superpose eq75 eq75
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq93 eq8
  subsumption eq119 eq93


@[equational_result]
theorem Equation34787_implies_Equation2 (G : Type*) [Magma G] (h : Equation34787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ X4) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X2 ◇ X3) = (((X4 ◇ (((X4 ◇ X0) ◇ X1) ◇ X5)) ◇ (((X0 ◇ X1) ◇ X3) ◇ X6)) ◇ X7) := superpose eq12 eq12
  have eq45 (X0 X1 X2 X3 X7 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ X7) := superpose eq12 eq28
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq45
  have eq149 (X0 X4 : G) : X0 = X4 := superpose eq7 eq60
  have eq290 (X0 : G) : sK0 ≠ X0 := superpose eq149 eq8
  subsumption eq290 eq149


@[equational_result]
theorem Equation34788_implies_Equation2 (G : Type*) [Magma G] (h : Equation34788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X4 := superpose eq7 eq11
  have eq23 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq13 eq11
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation34789_implies_Equation2 (G : Type*) [Magma G] (h : Equation34789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X5) ◇ X6)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X6 X7 : G) : ((X0 ◇ (X0 ◇ X6)) ◇ X7) = X4 := superpose eq7 eq9
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation34791_implies_Equation2 (G : Type*) [Magma G] (h : Equation34791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq15 eq15
  have eq162 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq162 eq8
  subsumption eq190 eq162


@[equational_result]
theorem Equation34792_implies_Equation2 (G : Type*) [Magma G] (h : Equation34792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq107 eq32


@[equational_result]
theorem Equation34793_implies_Equation2 (G : Type*) [Magma G] (h : Equation34793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X3) ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X4) := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ X0) = (X0 ◇ X4) := superpose eq9 eq11
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq13
  have eq27 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X4) = X2 := superpose eq13 eq7
  have eq29 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq9
  have eq49 (X2 X4 : G) : (X2 ◇ X4) = X2 := superpose eq29 eq27
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq49 eq19
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq49 eq50
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq49 eq61
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq68 eq63


@[equational_result]
theorem Equation34795_implies_Equation2 (G : Type*) [Magma G] (h : Equation34795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq14 eq14
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq132 eq90


@[equational_result]
theorem Equation34797_implies_Equation2 (G : Type*) [Magma G] (h : Equation34797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X0) ◇ X1) = (X0 ◇ X4) := superpose eq7 eq7
  have eq23 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X0 := superpose eq12 eq7
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq23 eq7
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq48 eq39


@[equational_result]
theorem Equation34799_implies_Equation2 (G : Type*) [Magma G] (h : Equation34799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X1) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3)))) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3)))) ◇ ((X2 ◇ X1) ◇ ((X4 ◇ X1) ◇ X4))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3)) = ((X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3))) ◇ X2)) ◇ (X0 ◇ ((X4 ◇ X1) ◇ X4))) := superpose eq7 eq9
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X4)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X4))) ◇ (X0 ◇ (X3 ◇ ((X5 ◇ X0) ◇ X5)))))) ◇ X1) = X2 := superpose eq9 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) = (X0 ◇ ((X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) ◇ X1) ◇ ((X4 ◇ X1) ◇ X4))) ◇ X0)) := superpose eq10 eq10
  have eq49 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) ◇ X1)) := superpose eq9 eq11
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ ((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X4))))) ◇ X2)) := superpose eq10 eq11
  have eq54 (X0 X1 X2 X3 X4 : G) : (((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X3)) ◇ ((X4 ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = X4 := superpose eq11 eq9
  have eq833 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))))) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))))) := superpose eq50 eq11
  have eq916 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X3)))) ◇ (X1 ◇ ((X4 ◇ X0) ◇ X4))) := superpose eq9 eq16
  have eq1027 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = ((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq916 eq916
  have eq1028 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq12 eq916
  have eq1029 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ (X1 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X0) = X1 := superpose eq916 eq7
  have eq1299 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq1028 eq1028
  have eq1308 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq11 eq1028
  have eq1331 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) := superpose eq1028 eq11
  have eq1687 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ ((X3 ◇ X1) ◇ X3)) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq1027 eq1028
  have eq2410 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq1299
  have eq3151 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((X3 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) := superpose eq1308 eq1308
  have eq3152 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X1)) := superpose eq1308 eq11
  have eq3306 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ X4) ◇ ((((((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ ((X6 ◇ X1) ◇ X6))) ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))))))) ◇ X3) = X4 := superpose eq35 eq30
  have eq3457 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ X4) ◇ ((((((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ ((X6 ◇ X1) ◇ X6))) ◇ X1))) ◇ X3) = X4 := superpose eq7 eq3306
  have eq3458 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq1028 eq3151
  have eq3526 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ X0) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (X4 ◇ (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) = (((X0 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ X0) ◇ ((((((X0 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ X0) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (X4 ◇ (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) := superpose eq50 eq54
  have eq3558 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5)) = ((((((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5))) ◇ X4)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3)) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)))) := superpose eq54 eq54
  have eq3598 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) = (((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3) ◇ (((((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) ◇ ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) := superpose eq54 eq35
  have eq3611 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1))) := superpose eq54 eq49
  have eq3692 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5)) = ((((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5))) ◇ X4)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3)) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)))) := superpose eq3458 eq3558
  have eq3703 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = (X0 ◇ ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) ◇ ((X4 ◇ X0) ◇ X4))) := superpose eq7 eq3458
  have eq3706 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq1299 eq3458
  have eq3730 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3) ◇ (((((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) ◇ ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) = (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X2 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2))) := superpose eq3703 eq3598
  have eq3731 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3) ◇ (((((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) ◇ ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) := superpose eq11 eq3730
  have eq3733 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5))) ◇ X4)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3)) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)))) := superpose eq3706 eq3692
  have eq3735 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq3706 eq1331
  have eq3736 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq3706 eq2410
  have eq3747 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1))) = ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X1 ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)))) := superpose eq3735 eq3611
  have eq3749 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1))) = ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq11 eq3747
  have eq3750 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq3736 eq3706
  have eq3752 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3))) ◇ X5))) ◇ X4)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3)) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)))) := superpose eq3750 eq3733
  have eq3775 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq3750 eq3735
  have eq3776 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq3750 eq3736
  have eq3876 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3) ◇ ((((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) ◇ ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) := superpose eq3776 eq3731
  have eq3880 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq3776 eq3775
  have eq3897 (X1 X2 X3 : G) : (X3 ◇ X1) = ((X3 ◇ ((X3 ◇ X1) ◇ X3)) ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq3880 eq1687
  have eq3919 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1))) := superpose eq3880 eq3749
  have eq3937 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))))) := superpose eq3880 eq833
  have eq3953 (X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (X4 ◇ (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) = ((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ (((((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (X4 ◇ (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) := superpose eq3880 eq3526
  have eq3957 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2))) := superpose eq3880 eq3876
  have eq4045 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X5))) ◇ X4)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)))) := superpose eq3880 eq3752
  have eq5439 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) = ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq3880 eq3919
  have eq5440 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq3880 eq5439
  have eq5441 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3))))) := superpose eq3776 eq5440
  have eq5442 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))))) := superpose eq3880 eq5441
  have eq5443 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) := superpose eq3750 eq5442
  have eq5444 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq3776 eq5443
  have eq5445 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq3776 eq5444
  have eq5524 (X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3)) ◇ (X4 ◇ (((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) = ((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ ((((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) := superpose eq10 eq3953
  have eq5525 (X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) = (((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) ◇ (X4 ◇ (((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) := superpose eq3880 eq5524
  have eq5526 (X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) = ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (X4 ◇ (((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) := superpose eq3776 eq5525
  have eq5527 (X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (X4 ◇ (((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) := superpose eq3776 eq5526
  have eq5533 (X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) := superpose eq3880 eq3957
  have eq5534 (X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)))) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) := superpose eq3880 eq5533
  have eq5535 (X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) := superpose eq3776 eq5534
  have eq5536 (X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) := superpose eq3880 eq5535
  have eq5537 (X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq3776 eq5536
  have eq5538 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) := superpose eq3776 eq5537
  have eq5683 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X5 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X5))) ◇ X4)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq5538 eq4045
  have eq5684 (X1 X2 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ X5))) ◇ X4)) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq3880 eq5683
  have eq5685 (X1 X2 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5))) ◇ X4)) ◇ (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq5538 eq5684
  have eq5686 (X1 X2 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X4 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5))) ◇ X4)) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq3776 eq5685
  have eq5687 (X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5))) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq3880 eq5686
  have eq5688 (X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq3880 eq5687
  have eq5689 (X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq5688
  have eq5690 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq5689 eq5445
  have eq5776 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) := superpose eq5690 eq3152
  have eq5790 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) = ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))))) := superpose eq5690 eq3937
  have eq5823 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X4) ◇ X5)))) = X3 := superpose eq5690 eq5527
  have eq5856 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq5690 eq5776
  have eq5883 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq5823 eq5790
  have eq5891 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq5883 eq5856
  have eq5909 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X1) ◇ ((X4 ◇ X1) ◇ X4))) = X2 := superpose eq5891 eq12
  have eq6222 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X0) = X1 := superpose eq5891 eq1029
  have eq6625 (X0 X1 X3 X4 X5 X6 : G) : (((X3 ◇ X4) ◇ ((((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ ((X6 ◇ X1) ◇ X6)) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ ((X6 ◇ X1) ◇ X6))) ◇ X1))) ◇ X3) = X4 := superpose eq5891 eq3457
  have eq6629 (X1 X3 : G) : (X3 ◇ X1) = ((X3 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1) := superpose eq5891 eq3897
  have eq6839 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X1) ◇ X1)) = X2 := superpose eq5891 eq5909
  have eq7135 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq5891 eq6222
  have eq8292 (X0 X1 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ ((((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ X1) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) ◇ X1)) ◇ X1))) ◇ X3) = X4 := superpose eq5891 eq6625
  have eq8293 (X0 X1 X3 X4 : G) : (((X3 ◇ X4) ◇ ((((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ ((X4 ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) ◇ X3) = X4 := superpose eq5891 eq8292
  have eq8299 (X1 X3 : G) : (X3 ◇ X1) = ((X3 ◇ X1) ◇ X1) := superpose eq5891 eq6629
  have eq8300 (X0 X1 X3 X4 : G) : (((X3 ◇ X4) ◇ (((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ X1) ◇ ((X4 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) ◇ X3) = X4 := superpose eq8299 eq8293
  have eq8464 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X1) ◇ X1)) = X2 := superpose eq8299 eq6839
  have eq8551 (X0 X1 X3 X4 : G) : (((X3 ◇ X4) ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ ((X4 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) ◇ X1))) ◇ X3) = X4 := superpose eq8299 eq8300
  have eq8552 (X0 X1 X3 X4 : G) : (((X3 ◇ X4) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) ◇ X1))) ◇ X3) = X4 := superpose eq8299 eq8551
  have eq8553 (X0 X1 X3 X4 : G) : (((X3 ◇ X4) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1))) ◇ X3) = X4 := superpose eq8299 eq8552
  have eq8845 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X1)) = X2 := superpose eq8299 eq8464
  have eq8846 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq8845 eq7135
  have eq8847 (X0 X1 X3 X4 : G) : (((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X4 := superpose eq8846 eq8553
  have eq9017 (X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = X4 := superpose eq8846 eq8847
  have eq9018 (X3 X4 : G) : (X3 ◇ X3) = X4 := superpose eq8846 eq9017
  have eq9050 (X0 X2 : G) : X0 = X2 := superpose eq9018 eq9018
  have eq9052 (X0 : G) : sK0 ≠ X0 := superpose eq9050 eq8
  subsumption eq9052 eq9050


@[equational_result]
theorem Equation34800_implies_Equation2 (G : Type*) [Magma G] (h : Equation34800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq105 eq36


@[equational_result]
theorem Equation34801_implies_Equation2 (G : Type*) [Magma G] (h : Equation34801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X3) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X4)))) ◇ X5) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ X4) := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ X4) := superpose eq9 eq11
  have eq24 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq13 eq7
  have eq35 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X5) = X2 := superpose eq24 eq10
  have eq41 (X1 X2 X5 : G) : (X1 ◇ X5) = X2 := superpose eq24 eq35
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq52 eq43


@[equational_result]
theorem Equation34803_implies_Equation2 (G : Type*) [Magma G] (h : Equation34803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq15 eq15
  have eq121 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq248 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq248 eq121


@[equational_result]
theorem Equation34804_implies_Equation2 (G : Type*) [Magma G] (h : Equation34804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X2) ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq129 eq45


@[equational_result]
theorem Equation34805_implies_Equation2 (G : Type*) [Magma G] (h : Equation34805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X3) ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X5) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation34806_implies_Equation2 (G : Type*) [Magma G] (h : Equation34806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ ((X5 ◇ X4) ◇ X6)) ◇ X7) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X6 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X6) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X6 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ X6) := superpose eq9 eq11
  have eq24 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X5) = X0 := superpose eq13 eq7
  have eq33 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq24 eq7
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq47 eq38


@[equational_result]
theorem Equation34808_implies_Equation2 (G : Type*) [Magma G] (h : Equation34808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq14 eq14
  have eq55 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq37 eq7
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq10 eq55
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq85 eq56


@[equational_result]
theorem Equation34810_implies_Equation2 (G : Type*) [Magma G] (h : Equation34810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X1) ◇ X0) = (X0 ◇ X4) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation34812_implies_Equation2 (G : Type*) [Magma G] (h : Equation34812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq13 eq13
  have eq52 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq37 eq7
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq10 eq52
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq79 eq61


@[equational_result]
theorem Equation34814_implies_Equation2 (G : Type*) [Magma G] (h : Equation34814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ X4) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation34818_implies_Equation2 (G : Type*) [Magma G] (h : Equation34818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X1) ◇ X2) = (X0 ◇ X4) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq172 eq55


@[equational_result]
theorem Equation34820_implies_Equation2 (G : Type*) [Magma G] (h : Equation34820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq42 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq14 eq14
  have eq60 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq42 eq7
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq10 eq60
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq90 eq61


@[equational_result]
theorem Equation34821_implies_Equation2 (G : Type*) [Magma G] (h : Equation34821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq19 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X4))) = X4 := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X4))) ◇ X5) ◇ X6) ◇ X3) ◇ X0) = X6 := superpose eq7 eq11
  have eq27 (X0 X3 X4 X5 X6 : G) : ((((X4 ◇ X5) ◇ X6) ◇ X3) ◇ X0) = X6 := superpose eq19 eq21
  have eq28 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = X4 := superpose eq27 eq11
  have eq32 (X0 X5 : G) : X0 = X5 := superpose eq7 eq28
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq45 eq32


@[equational_result]
theorem Equation34822_implies_Equation2 (G : Type*) [Magma G] (h : Equation34822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X5) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X3) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq10
  have eq23 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = X4 := superpose eq15 eq11
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation34823_implies_Equation2 (G : Type*) [Magma G] (h : Equation34823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : ((X2 ◇ X1) ◇ X3) = (X0 ◇ X6) := superpose eq7 eq7
  have eq16 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation34825_implies_Equation2 (G : Type*) [Magma G] (h : Equation34825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) = X0 := superpose eq9 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq9 eq7
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq10
  have eq62 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq34 eq10
  have eq76 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq62 eq36
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X1 := superpose eq76 eq9
  have eq94 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq76 eq33
  have eq110 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X1 := superpose eq76 eq79
  have eq139 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq76 eq94
  have eq140 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq62 eq139
  have eq141 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq140 eq34
  have eq149 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq141 eq76
  have eq150 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq141 eq110
  have eq164 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X0)) = X1 := superpose eq149 eq150
  have eq165 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X1) = X1 := superpose eq149 eq164
  have eq166 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq149 eq165
  have eq177 (X0 X1 : G) : X0 = X1 := superpose eq166 eq149
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq177 eq8
  subsumption eq179 eq177


@[equational_result]
theorem Equation34826_implies_Equation2 (G : Type*) [Magma G] (h : Equation34826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq17 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq27 eq18


@[equational_result]
theorem Equation34827_implies_Equation2 (G : Type*) [Magma G] (h : Equation34827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq114 eq49


@[equational_result]
theorem Equation34831_implies_Equation2 (G : Type*) [Magma G] (h : Equation34831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X5) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : ((X2 ◇ X2) ◇ X1) = (X0 ◇ X4) := superpose eq7 eq7
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq12 eq10
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation34834_implies_Equation2 (G : Type*) [Magma G] (h : Equation34834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation34835_implies_Equation2 (G : Type*) [Magma G] (h : Equation34835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq130 eq47


@[equational_result]
theorem Equation34837_implies_Equation2 (G : Type*) [Magma G] (h : Equation34837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq10 eq10
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq136 eq57


@[equational_result]
theorem Equation34838_implies_Equation2 (G : Type*) [Magma G] (h : Equation34838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X4) ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq60 eq42


@[equational_result]
theorem Equation34839_implies_Equation2 (G : Type*) [Magma G] (h : Equation34839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq10 eq10
  have eq19 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X0 := superpose eq15 eq7
  have eq25 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq15 eq19
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation34840_implies_Equation2 (G : Type*) [Magma G] (h : Equation34840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation34842_implies_Equation2 (G : Type*) [Magma G] (h : Equation34842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq116 eq41


@[equational_result]
theorem Equation34843_implies_Equation2 (G : Type*) [Magma G] (h : Equation34843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X2)) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq9
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq119 eq37


@[equational_result]
theorem Equation34844_implies_Equation2 (G : Type*) [Magma G] (h : Equation34844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq14 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq31 eq22


@[equational_result]
theorem Equation34845_implies_Equation2 (G : Type*) [Magma G] (h : Equation34845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ X6) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq114 eq49


@[equational_result]
theorem Equation34847_implies_Equation2 (G : Type*) [Magma G] (h : Equation34847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq100 eq35


@[equational_result]
theorem Equation34848_implies_Equation2 (G : Type*) [Magma G] (h : Equation34848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)))) ◇ X4) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq11 eq11
  have eq23 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X4) = X2 := superpose eq16 eq9
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation34849_implies_Equation2 (G : Type*) [Magma G] (h : Equation34849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X4 ◇ X1) ◇ X3)) = X2 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq119 eq42


@[equational_result]
theorem Equation34850_implies_Equation2 (G : Type*) [Magma G] (h : Equation34850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ X6) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation34852_implies_Equation2 (G : Type*) [Magma G] (h : Equation34852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X3 := superpose eq11 eq7
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq170 eq70


@[equational_result]
theorem Equation34853_implies_Equation2 (G : Type*) [Magma G] (h : Equation34853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X4)) ◇ X4) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation34854_implies_Equation2 (G : Type*) [Magma G] (h : Equation34854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq78 eq22


@[equational_result]
theorem Equation34855_implies_Equation2 (G : Type*) [Magma G] (h : Equation34855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ X6) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation34857_implies_Equation2 (G : Type*) [Magma G] (h : Equation34857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq120 eq41


@[equational_result]
theorem Equation34858_implies_Equation2 (G : Type*) [Magma G] (h : Equation34858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X5)) ◇ X4) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation34859_implies_Equation2 (G : Type*) [Magma G] (h : Equation34859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation34860_implies_Equation2 (G : Type*) [Magma G] (h : Equation34860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ X6) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation34862_implies_Equation2 (G : Type*) [Magma G] (h : Equation34862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq128 eq41


@[equational_result]
theorem Equation34863_implies_Equation2 (G : Type*) [Magma G] (h : Equation34863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X5 X6 X7 : G) : ((X0 ◇ ((X5 ◇ X6) ◇ X7)) ◇ X5) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation34864_implies_Equation2 (G : Type*) [Magma G] (h : Equation34864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X5 X6 X7 : G) : ((X0 ◇ ((X5 ◇ X6) ◇ X7)) ◇ X6) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation34865_implies_Equation2 (G : Type*) [Magma G] (h : Equation34865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ ((X5 ◇ X6) ◇ X7)) ◇ X7) = X4 := superpose eq7 eq7
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq53 eq33


@[equational_result]
theorem Equation34866_implies_Equation2 (G : Type*) [Magma G] (h : Equation34866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X8 : G) : (((X1 ◇ X2) ◇ X0) ◇ X8) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq11 eq11
  have eq49 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation34869_implies_Equation2 (G : Type*) [Magma G] (h : Equation34869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq124 eq39


@[equational_result]
theorem Equation34872_implies_Equation2 (G : Type*) [Magma G] (h : Equation34872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation34874_implies_Equation2 (G : Type*) [Magma G] (h : Equation34874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq10
  have eq25 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq7
  have eq31 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq25 eq9
  have eq43 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq31
  have eq47 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq43 eq7
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq47 eq47
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq54 eq52


@[equational_result]
theorem Equation34875_implies_Equation2 (G : Type*) [Magma G] (h : Equation34875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) = X1 := superpose eq10 eq7
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq15
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq46
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq156 eq57


@[equational_result]
theorem Equation34876_implies_Equation2 (G : Type*) [Magma G] (h : Equation34876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34879_implies_Equation2 (G : Type*) [Magma G] (h : Equation34879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))))) ◇ X2)) ◇ X4) = X2 := superpose eq7 eq9
  have eq25 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq14
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq132 eq41


@[equational_result]
theorem Equation34882_implies_Equation2 (G : Type*) [Magma G] (h : Equation34882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) := superpose eq7 eq7
  have eq36 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X3 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2)))) ◇ X4) = X3 := superpose eq10 eq7
  have eq43 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq7 eq36
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq7 eq43
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq153 eq59


@[equational_result]
theorem Equation34884_implies_Equation2 (G : Type*) [Magma G] (h : Equation34884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := superpose eq7 eq9
  have eq42 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X4)) := superpose eq9 eq10
  have eq62 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X3)) ◇ X1) := superpose eq23 eq9
  have eq63 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq23 eq7
  have eq71 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq63 eq62
  have eq92 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq71 eq10
  have eq107 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X4)) := superpose eq92 eq42
  have eq108 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq71 eq107
  have eq110 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq108 eq71
  have eq111 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq108 eq92
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq110 eq111
  have eq116 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq110 eq115
  have eq122 (X0 X2 : G) : X0 = X2 := superpose eq116 eq116
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq124 eq122


@[equational_result]
theorem Equation34886_implies_Equation2 (G : Type*) [Magma G] (h : Equation34886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X3 ◇ ((X4 ◇ X4) ◇ (X0 ◇ X5))) ◇ X6)) ◇ X7) = X3 := superpose eq7 eq9
  have eq27 (X0 X3 X7 : G) : (X0 ◇ X7) = X3 := superpose eq7 eq14
  have eq75 (X0 X4 : G) : X0 = X4 := superpose eq7 eq27
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq165 eq75


@[equational_result]
theorem Equation34890_implies_Equation2 (G : Type*) [Magma G] (h : Equation34890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq139 eq52


@[equational_result]
theorem Equation34892_implies_Equation2 (G : Type*) [Magma G] (h : Equation34892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation34894_implies_Equation2 (G : Type*) [Magma G] (h : Equation34894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation34897_implies_Equation2 (G : Type*) [Magma G] (h : Equation34897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) = (((X1 ◇ X1) ◇ (X0 ◇ X3)) ◇ X3) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) = X0 := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) ◇ X2) = X1 := superpose eq9 eq7
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) = X1 := superpose eq9 eq18
  have eq40 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) := superpose eq18 eq7
  have eq46 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq18 eq35
  have eq48 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) = X1 := superpose eq46 eq25
  have eq62 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X2) = X1 := superpose eq46 eq48
  have eq77 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq62 eq40
  have eq78 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq46 eq77
  have eq79 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq78 eq46
  have eq83 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq79 eq62
  have eq89 (X0 X2 : G) : X0 = X2 := superpose eq83 eq83
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq101 eq89


@[equational_result]
theorem Equation34898_implies_Equation2 (G : Type*) [Magma G] (h : Equation34898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq166 eq52


@[equational_result]
theorem Equation34900_implies_Equation2 (G : Type*) [Magma G] (h : Equation34900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq44 eq42


@[equational_result]
theorem Equation34901_implies_Equation2 (G : Type*) [Magma G] (h : Equation34901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation34902_implies_Equation2 (G : Type*) [Magma G] (h : Equation34902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34903_implies_Equation2 (G : Type*) [Magma G] (h : Equation34903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34906_implies_Equation2 (G : Type*) [Magma G] (h : Equation34906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq14
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq84 eq50


@[equational_result]
theorem Equation34909_implies_Equation2 (G : Type*) [Magma G] (h : Equation34909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq9
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq75 eq53


@[equational_result]
theorem Equation34911_implies_Equation2 (G : Type*) [Magma G] (h : Equation34911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((((((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X1) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq10 eq10
  have eq27 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4))) ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4))) = X1 := superpose eq7 eq9
  have eq47 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := superpose eq7 eq18
  have eq48 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X1 ◇ X3)) ◇ X4) = X0 := superpose eq9 eq18
  have eq68 (X0 X1 X2 X4 : G) : (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X4)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq18 eq9
  have eq105 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq47 eq11
  have eq112 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4))) = X1 := superpose eq47 eq27
  have eq116 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4))) = X1 := superpose eq47 eq112
  have eq117 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X4) = X0 := superpose eq47 eq48
  have eq120 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq68 eq15
  have eq131 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X4))) = X1 := superpose eq120 eq116
  have eq137 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq120 eq16
  have eq164 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq120 eq131
  have eq166 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq120 eq137
  have eq167 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq120 eq166
  have eq168 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq164 eq167
  have eq172 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq168 eq105
  have eq177 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X4) = X0 := superpose eq172 eq117
  have eq185 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq172 eq177
  have eq186 (X0 X3 : G) : X0 = X3 := superpose eq185 eq185
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq186 eq8
  subsumption eq191 eq186


@[equational_result]
theorem Equation34913_implies_Equation2 (G : Type*) [Magma G] (h : Equation34913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq74 eq20


@[equational_result]
theorem Equation34916_implies_Equation2 (G : Type*) [Magma G] (h : Equation34916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation34918_implies_Equation2 (G : Type*) [Magma G] (h : Equation34918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation34919_implies_Equation2 (G : Type*) [Magma G] (h : Equation34919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34921_implies_Equation2 (G : Type*) [Magma G] (h : Equation34921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation34922_implies_Equation2 (G : Type*) [Magma G] (h : Equation34922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation34923_implies_Equation2 (G : Type*) [Magma G] (h : Equation34923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34925_implies_Equation2 (G : Type*) [Magma G] (h : Equation34925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq27 eq12


@[equational_result]
theorem Equation34926_implies_Equation2 (G : Type*) [Magma G] (h : Equation34926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq14 eq15
  have eq25 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ ((X3 ◇ X4) ◇ X0)))) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ ((X3 ◇ X4) ◇ X0))))) ◇ X0) ◇ X2) = X4 := superpose eq7 eq9
  have eq56 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X1) ◇ X2) := superpose eq14 eq14
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) = X0 := superpose eq10 eq14
  have eq63 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2))) ◇ (X2 ◇ X3)) ◇ X1) = X3 := superpose eq14 eq9
  have eq77 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1))) ◇ X2) ◇ ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ X3) ◇ X2)) = X3 := superpose eq14 eq10
  have eq105 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1))) ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X2)) = X3 := superpose eq14 eq77
  have eq120 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq58 eq58
  have eq147 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X2)) = X3 := superpose eq120 eq105
  have eq150 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X3 := superpose eq120 eq63
  have eq177 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((((X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) ◇ X2) ◇ X0) := superpose eq18 eq10
  have eq223 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((((X1 ◇ X1) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) ◇ X2) ◇ X0) := superpose eq56 eq177
  have eq224 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) := superpose eq120 eq223
  have eq270 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq120 eq10
  have eq271 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = X0 := superpose eq120 eq7
  have eq319 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq271 eq270
  have eq322 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X3 := superpose eq319 eq150
  have eq332 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X3) ◇ X2)) = X3 := superpose eq322 eq147
  have eq350 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) := superpose eq332 eq224
  have eq359 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X1 ◇ X0) := superpose eq322 eq350
  have eq424 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ ((X3 ◇ X4) ◇ X0)))) ◇ X0) ◇ X2) = X4 := superpose eq359 eq25
  have eq537 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X4 := superpose eq359 eq424
  have eq538 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X2) = X4 := superpose eq359 eq537
  have eq541 (X0 X4 : G) : X0 = X4 := superpose eq538 eq538
  have eq543 (X0 : G) : sK0 ≠ X0 := superpose eq541 eq8
  subsumption eq543 eq541


@[equational_result]
theorem Equation34927_implies_Equation2 (G : Type*) [Magma G] (h : Equation34927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X4) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation34929_implies_Equation2 (G : Type*) [Magma G] (h : Equation34929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34930_implies_Equation2 (G : Type*) [Magma G] (h : Equation34930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34931_implies_Equation2 (G : Type*) [Magma G] (h : Equation34931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34933_implies_Equation2 (G : Type*) [Magma G] (h : Equation34933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34934_implies_Equation2 (G : Type*) [Magma G] (h : Equation34934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34935_implies_Equation2 (G : Type*) [Magma G] (h : Equation34935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34937_implies_Equation2 (G : Type*) [Magma G] (h : Equation34937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34938_implies_Equation2 (G : Type*) [Magma G] (h : Equation34938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34939_implies_Equation2 (G : Type*) [Magma G] (h : Equation34939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34940_implies_Equation2 (G : Type*) [Magma G] (h : Equation34940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34942_implies_Equation2 (G : Type*) [Magma G] (h : Equation34942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq9 eq10
  have eq46 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq29 eq27
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq9 eq46
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq57 eq11
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq78 eq73


@[equational_result]
theorem Equation34944_implies_Equation2 (G : Type*) [Magma G] (h : Equation34944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq127 eq37


@[equational_result]
theorem Equation34946_implies_Equation2 (G : Type*) [Magma G] (h : Equation34946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation34948_implies_Equation2 (G : Type*) [Magma G] (h : Equation34948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation34952_implies_Equation2 (G : Type*) [Magma G] (h : Equation34952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq172 eq57


@[equational_result]
theorem Equation34954_implies_Equation2 (G : Type*) [Magma G] (h : Equation34954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation34955_implies_Equation2 (G : Type*) [Magma G] (h : Equation34955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation34956_implies_Equation2 (G : Type*) [Magma G] (h : Equation34956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation34957_implies_Equation2 (G : Type*) [Magma G] (h : Equation34957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation34959_implies_Equation2 (G : Type*) [Magma G] (h : Equation34959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation34961_implies_Equation2 (G : Type*) [Magma G] (h : Equation34961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq10
  have eq21 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq12 eq11
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq45 eq23


@[equational_result]
theorem Equation34963_implies_Equation2 (G : Type*) [Magma G] (h : Equation34963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34964_implies_Equation2 (G : Type*) [Magma G] (h : Equation34964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34965_implies_Equation2 (G : Type*) [Magma G] (h : Equation34965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34967_implies_Equation2 (G : Type*) [Magma G] (h : Equation34967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34968_implies_Equation2 (G : Type*) [Magma G] (h : Equation34968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34969_implies_Equation2 (G : Type*) [Magma G] (h : Equation34969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34971_implies_Equation2 (G : Type*) [Magma G] (h : Equation34971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34972_implies_Equation2 (G : Type*) [Magma G] (h : Equation34972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34973_implies_Equation2 (G : Type*) [Magma G] (h : Equation34973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34974_implies_Equation2 (G : Type*) [Magma G] (h : Equation34974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation34976_implies_Equation2 (G : Type*) [Magma G] (h : Equation34976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq9 eq7
  have eq21 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq9
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := superpose eq21 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq21 eq22
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq25 eq25
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq25 eq28
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq46 eq36


@[equational_result]
theorem Equation34977_implies_Equation2 (G : Type*) [Magma G] (h : Equation34977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq13 eq10
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation34978_implies_Equation2 (G : Type*) [Magma G] (h : Equation34978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation34980_implies_Equation2 (G : Type*) [Magma G] (h : Equation34980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34981_implies_Equation2 (G : Type*) [Magma G] (h : Equation34981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation34982_implies_Equation2 (G : Type*) [Magma G] (h : Equation34982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34984_implies_Equation2 (G : Type*) [Magma G] (h : Equation34984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34985_implies_Equation2 (G : Type*) [Magma G] (h : Equation34985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation34986_implies_Equation2 (G : Type*) [Magma G] (h : Equation34986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34988_implies_Equation2 (G : Type*) [Magma G] (h : Equation34988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34989_implies_Equation2 (G : Type*) [Magma G] (h : Equation34989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34990_implies_Equation2 (G : Type*) [Magma G] (h : Equation34990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34991_implies_Equation2 (G : Type*) [Magma G] (h : Equation34991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation34993_implies_Equation2 (G : Type*) [Magma G] (h : Equation34993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation34994_implies_Equation2 (G : Type*) [Magma G] (h : Equation34994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation34995_implies_Equation2 (G : Type*) [Magma G] (h : Equation34995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq9 eq9
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq103 eq35


@[equational_result]
theorem Equation34996_implies_Equation2 (G : Type*) [Magma G] (h : Equation34996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation34998_implies_Equation2 (G : Type*) [Magma G] (h : Equation34998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation34999_implies_Equation2 (G : Type*) [Magma G] (h : Equation34999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35000_implies_Equation2 (G : Type*) [Magma G] (h : Equation35000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35001_implies_Equation2 (G : Type*) [Magma G] (h : Equation35001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35003_implies_Equation2 (G : Type*) [Magma G] (h : Equation35003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35004_implies_Equation2 (G : Type*) [Magma G] (h : Equation35004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35005_implies_Equation2 (G : Type*) [Magma G] (h : Equation35005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35006_implies_Equation2 (G : Type*) [Magma G] (h : Equation35006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35008_implies_Equation2 (G : Type*) [Magma G] (h : Equation35008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35009_implies_Equation2 (G : Type*) [Magma G] (h : Equation35009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35010_implies_Equation2 (G : Type*) [Magma G] (h : Equation35010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35011_implies_Equation2 (G : Type*) [Magma G] (h : Equation35011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35013_implies_Equation2 (G : Type*) [Magma G] (h : Equation35013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35014_implies_Equation2 (G : Type*) [Magma G] (h : Equation35014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35015_implies_Equation2 (G : Type*) [Magma G] (h : Equation35015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35016_implies_Equation2 (G : Type*) [Magma G] (h : Equation35016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35017_implies_Equation2 (G : Type*) [Magma G] (h : Equation35017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35019_implies_Equation2 (G : Type*) [Magma G] (h : Equation35019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation35020_implies_Equation2 (G : Type*) [Magma G] (h : Equation35020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq40 eq13


@[equational_result]
theorem Equation35021_implies_Equation2 (G : Type*) [Magma G] (h : Equation35021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35023_implies_Equation2 (G : Type*) [Magma G] (h : Equation35023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq10
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq12
  have eq62 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq149 eq62


@[equational_result]
theorem Equation35025_implies_Equation2 (G : Type*) [Magma G] (h : Equation35025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation35027_implies_Equation2 (G : Type*) [Magma G] (h : Equation35027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq132 eq48


@[equational_result]
theorem Equation35028_implies_Equation2 (G : Type*) [Magma G] (h : Equation35028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq122 eq41


@[equational_result]
theorem Equation35029_implies_Equation2 (G : Type*) [Magma G] (h : Equation35029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35031_implies_Equation2 (G : Type*) [Magma G] (h : Equation35031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq57 eq17


@[equational_result]
theorem Equation35032_implies_Equation2 (G : Type*) [Magma G] (h : Equation35032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation35033_implies_Equation2 (G : Type*) [Magma G] (h : Equation35033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation35034_implies_Equation2 (G : Type*) [Magma G] (h : Equation35034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35037_implies_Equation2 (G : Type*) [Magma G] (h : Equation35037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (((((X0 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2))) ◇ X0) ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq9 eq7
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X2) ◇ X3)))) ◇ X0)) = X3 := superpose eq7 eq19
  have eq56 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2))) = X2 := superpose eq19 eq19
  have eq67 (X0 X2 X3 : G) : ((((X2 ◇ X0) ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq56 eq19
  have eq75 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq56 eq53
  have eq109 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq75 eq75
  have eq124 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X0 := superpose eq109 eq7
  have eq125 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X3)) ◇ X2) = X3 := superpose eq109 eq9
  have eq157 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq109 eq75
  have eq173 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) ◇ X2) = X3 := superpose eq109 eq125
  have eq253 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq67 eq124
  have eq276 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq124 eq173
  have eq300 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X1 := superpose eq157 eq276
  have eq312 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq276 eq300
  have eq316 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq312 eq253
  have eq392 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X2 := superpose eq312 eq316
  have eq393 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq312 eq392
  have eq394 (X0 X3 : G) : X0 = X3 := superpose eq393 eq393
  have eq399 (X0 : G) : sK0 ≠ X0 := superpose eq394 eq8
  subsumption eq399 eq394


@[equational_result]
theorem Equation35038_implies_Equation2 (G : Type*) [Magma G] (h : Equation35038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation35040_implies_Equation2 (G : Type*) [Magma G] (h : Equation35040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq27 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = (((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq10 eq7
  have eq41 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5)))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5))))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5)))) = X4 := superpose eq10 eq9
  have eq70 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose eq10 eq23
  have eq77 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X0) := superpose eq23 eq10
  have eq88 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ X4) := superpose eq70 eq27
  have eq98 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := superpose eq23 eq88
  have eq99 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq88 eq88
  have eq114 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose eq88 eq23
  have eq131 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X0 := superpose eq7 eq99
  have eq208 (X0 X2 X3 : G) : ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X2) = X0 := superpose eq131 eq114
  have eq213 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X1 := superpose eq208 eq98
  have eq217 (X0 X1 X3 : G) : (X1 ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq213 eq77
  have eq219 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq213 eq217
  have eq220 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq23 eq219
  have eq221 (X0 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ ((X3 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5))) ◇ ((X3 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5)))) ◇ ((X3 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5))) = X4 := superpose eq220 eq41
  have eq275 (X0 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X5))) ◇ (X0 ◇ X5)) = X4 := superpose eq220 eq221
  have eq276 (X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X5) ◇ X5)) ◇ X5) = X4 := superpose eq220 eq275
  have eq277 (X4 X5 : G) : (((X4 ◇ X5) ◇ X5) ◇ X5) = X4 := superpose eq220 eq276
  have eq278 (X4 X5 : G) : (X5 ◇ X5) = X4 := superpose eq220 eq277
  have eq300 (X0 X2 : G) : X0 = X2 := superpose eq278 eq278
  have eq302 (X0 : G) : sK0 ≠ X0 := superpose eq300 eq8
  subsumption eq302 eq300


@[equational_result]
theorem Equation35042_implies_Equation2 (G : Type*) [Magma G] (h : Equation35042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation35044_implies_Equation2 (G : Type*) [Magma G] (h : Equation35044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) = (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X4) ◇ (((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4)) ◇ X1) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X5) ◇ (((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X5)) ◇ X0) = ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) = ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3) = X0 := superpose eq10 eq7
  have eq41 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) = X2 := superpose eq30 eq29
  have eq43 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq11
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq10 eq11
  have eq64 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X2 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq7 eq44
  have eq163 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq41 eq30
  have eq166 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X3) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) := superpose eq41 eq10
  have eq182 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3)) = ((X0 ◇ X0) ◇ X2) := superpose eq166 eq16
  have eq184 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq182 eq15
  have eq225 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) = ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq184 eq184
  have eq273 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq184 eq30
  have eq696 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq64 eq273
  have eq733 (X0 X1 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose eq184 eq696
  have eq772 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq273 eq33
  have eq826 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ (((((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0) ◇ X1) ◇ X0)) ◇ (((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0))) ◇ (((((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0) ◇ X1) ◇ X0)) = X3 := superpose eq33 eq9
  have eq878 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq163 eq772
  have eq896 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq184 eq733
  have eq1052 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq43 eq878
  have eq1112 (X0 X1 : G) : (X1 ◇ X0) = ((((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq225 eq1052
  have eq1113 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq896 eq1112
  have eq1114 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq273 eq1113
  have eq1117 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0) ◇ X1)) ◇ (((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0))) ◇ ((((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0) ◇ X1)) = X3 := superpose eq1114 eq826
  have eq1601 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ (((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0)) ◇ (((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0))) ◇ (((X0 ◇ X4) ◇ (X2 ◇ X4)) ◇ X0)) = X3 := superpose eq1114 eq1117
  have eq1602 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ X4) ◇ (X2 ◇ X4))) ◇ ((X0 ◇ X4) ◇ (X2 ◇ X4)))) ◇ ((X0 ◇ X4) ◇ (X2 ◇ X4))) = X3 := superpose eq1114 eq1601
  have eq1603 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ (X0 ◇ X4))) ◇ (X0 ◇ X4)) = X3 := superpose eq1114 eq1602
  have eq1604 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X0)) ◇ X0) = X3 := superpose eq1114 eq1603
  have eq1605 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := superpose eq1114 eq1604
  have eq1606 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq1114 eq1605
  have eq1607 (X0 X3 : G) : X0 = X3 := superpose eq1606 eq1606
  have eq1609 (X0 : G) : sK0 ≠ X0 := superpose eq1607 eq8
  subsumption eq1609 eq1607


@[equational_result]
theorem Equation35046_implies_Equation2 (G : Type*) [Magma G] (h : Equation35046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation35048_implies_Equation2 (G : Type*) [Magma G] (h : Equation35048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) = (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq51 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (X0 ◇ X4) = ((((((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X7) ◇ X8) ◇ ((X0 ◇ X5) ◇ (X2 ◇ X6))) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X7)) := superpose eq10 eq11
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11
  have eq62 (X0 X1 X2 X3 X5 X6 : G) : (((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X5 ◇ X1) ◇ X6)) ◇ X1) = X5 := superpose eq11 eq7
  have eq84 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4) = X0 := superpose eq7 eq61
  have eq99 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) ◇ X2) = X0 := superpose eq61 eq7
  have eq141 (X0 X2 X4 X5 X6 X8 : G) : (X0 ◇ X4) = (((X2 ◇ X8) ◇ ((X0 ◇ X5) ◇ (X2 ◇ X6))) ◇ X2) := superpose eq84 eq51
  have eq147 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq99 eq141
  have eq154 (X0 X1 X2 X3 X5 X6 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ ((X5 ◇ X1) ◇ X6)) ◇ X1) = X5 := superpose eq147 eq62
  have eq218 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X5 := superpose eq147 eq154
  have eq219 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) = X5 := superpose eq147 eq218
  have eq220 (X0 X1 X2 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = X5 := superpose eq147 eq219
  have eq221 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X1) = X5 := superpose eq147 eq220
  have eq222 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq147 eq221
  have eq223 (X0 X3 : G) : X0 = X3 := superpose eq222 eq222
  have eq242 (X0 : G) : sK0 ≠ X0 := superpose eq223 eq8
  subsumption eq242 eq223


@[equational_result]
theorem Equation35049_implies_Equation2 (G : Type*) [Magma G] (h : Equation35049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X4 ◇ ((X5 ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X7))) ◇ X8)) ◇ X6) = X5 := superpose eq11 eq9
  have eq52 (X0 X1 X2 X3 X4 X6 X8 : G) : ((X4 ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ X8)) ◇ X6) = X1 := superpose eq11 eq9
  have eq70 (X1 X4 X5 X6 : G) : ((X4 ◇ X1) ◇ X6) = X5 := superpose eq52 eq38
  have eq226 (X0 X4 : G) : X0 = X4 := superpose eq7 eq70
  have eq392 (X0 : G) : sK0 ≠ X0 := superpose eq226 eq8
  subsumption eq392 eq226


@[equational_result]
theorem Equation35050_implies_Equation2 (G : Type*) [Magma G] (h : Equation35050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation35051_implies_Equation2 (G : Type*) [Magma G] (h : Equation35051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq66 eq13


@[equational_result]
theorem Equation35054_implies_Equation2 (G : Type*) [Magma G] (h : Equation35054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq103 eq33


@[equational_result]
theorem Equation35055_implies_Equation2 (G : Type*) [Magma G] (h : Equation35055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation35059_implies_Equation2 (G : Type*) [Magma G] (h : Equation35059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation35062_implies_Equation2 (G : Type*) [Magma G] (h : Equation35062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq145 eq45


@[equational_result]
theorem Equation35063_implies_Equation2 (G : Type*) [Magma G] (h : Equation35063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation35065_implies_Equation2 (G : Type*) [Magma G] (h : Equation35065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X2)) = X1 := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X6)) ◇ X7) ◇ (((X0 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X5) ◇ X3))) = X2 := superpose eq12 eq12
  have eq47 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X7) ◇ X3)) = X2 := superpose eq12 eq12
  have eq68 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq47 eq43
  have eq76 (X0 X4 : G) : X0 = X4 := superpose eq7 eq68
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq182 eq76


@[equational_result]
theorem Equation35066_implies_Equation2 (G : Type*) [Magma G] (h : Equation35066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X2) ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq185 eq67


@[equational_result]
theorem Equation35067_implies_Equation2 (G : Type*) [Magma G] (h : Equation35067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X3) ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq185 eq61


@[equational_result]
theorem Equation35068_implies_Equation2 (G : Type*) [Magma G] (h : Equation35068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation35070_implies_Equation2 (G : Type*) [Magma G] (h : Equation35070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq39 eq17


@[equational_result]
theorem Equation35071_implies_Equation2 (G : Type*) [Magma G] (h : Equation35071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation35072_implies_Equation2 (G : Type*) [Magma G] (h : Equation35072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35073_implies_Equation2 (G : Type*) [Magma G] (h : Equation35073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35075_implies_Equation2 (G : Type*) [Magma G] (h : Equation35075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq75 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq176 eq75


@[equational_result]
theorem Equation35076_implies_Equation2 (G : Type*) [Magma G] (h : Equation35076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X1 ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq66 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq191 eq66


@[equational_result]
theorem Equation35077_implies_Equation2 (G : Type*) [Magma G] (h : Equation35077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq66 eq13


@[equational_result]
theorem Equation35078_implies_Equation2 (G : Type*) [Magma G] (h : Equation35078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation35080_implies_Equation2 (G : Type*) [Magma G] (h : Equation35080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq162 eq62


@[equational_result]
theorem Equation35081_implies_Equation2 (G : Type*) [Magma G] (h : Equation35081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X2)) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq9
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq169 eq55


@[equational_result]
theorem Equation35082_implies_Equation2 (G : Type*) [Magma G] (h : Equation35082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq9
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq185 eq59


@[equational_result]
theorem Equation35083_implies_Equation2 (G : Type*) [Magma G] (h : Equation35083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35085_implies_Equation2 (G : Type*) [Magma G] (h : Equation35085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation35086_implies_Equation2 (G : Type*) [Magma G] (h : Equation35086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ ((X0 ◇ X4) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation35087_implies_Equation2 (G : Type*) [Magma G] (h : Equation35087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation35088_implies_Equation2 (G : Type*) [Magma G] (h : Equation35088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35090_implies_Equation2 (G : Type*) [Magma G] (h : Equation35090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = X1 := superpose eq7 eq7
  have eq47 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq59 eq47


@[equational_result]
theorem Equation35091_implies_Equation2 (G : Type*) [Magma G] (h : Equation35091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 X6 : G) : (X0 ◇ ((X0 ◇ X5) ◇ X6)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation35092_implies_Equation2 (G : Type*) [Magma G] (h : Equation35092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35093_implies_Equation2 (G : Type*) [Magma G] (h : Equation35093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35094_implies_Equation2 (G : Type*) [Magma G] (h : Equation35094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X8 : G) : (X0 ◇ X8) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35096_implies_Equation2 (G : Type*) [Magma G] (h : Equation35096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ X3)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq9 eq7
  have eq21 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq17 eq10
  have eq31 (X0 X1 : G) : ((((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq9 eq21
  have eq37 (X0 X1 : G) : (((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq17 eq31
  have eq79 (X0 X1 X2 : G) : ((((X2 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq17 eq16
  have eq80 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X2) = X0 := superpose eq17 eq16
  have eq98 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) = X0 := superpose eq17 eq80
  have eq99 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq98 eq37
  have eq100 (X1 X2 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) = X1 := superpose eq99 eq79
  have eq150 (X1 X2 : G) : (((X2 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq99 eq100
  have eq151 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq99 eq150
  have eq152 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq99 eq151
  have eq159 (X0 X1 : G) : X0 = X1 := superpose eq99 eq152
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq161 eq159


@[equational_result]
theorem Equation35098_implies_Equation2 (G : Type*) [Magma G] (h : Equation35098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation35102_implies_Equation2 (G : Type*) [Magma G] (h : Equation35102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq68 eq15


@[equational_result]
theorem Equation35106_implies_Equation2 (G : Type*) [Magma G] (h : Equation35106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation35108_implies_Equation2 (G : Type*) [Magma G] (h : Equation35108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4) ◇ X5)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3))) = X4 := superpose eq7 eq7
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq9 eq7
  have eq69 (X0 X4 : G) : X0 = X4 := superpose eq7 eq58
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq173 eq69


@[equational_result]
theorem Equation35109_implies_Equation2 (G : Type*) [Magma G] (h : Equation35109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4) ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X4) = ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq57 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4) = X1 := superpose eq11 eq9
  have eq66 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ ((X2 ◇ X1) ◇ X5)) ◇ X0) ◇ X6)) = X3 := superpose eq9 eq7
  have eq92 (X0 X1 X3 X6 : G) : (X0 ◇ (X1 ◇ X6)) = X3 := superpose eq57 eq66
  have eq99 (X0 X5 : G) : X0 = X5 := superpose eq7 eq92
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq171 eq99


@[equational_result]
theorem Equation35110_implies_Equation2 (G : Type*) [Magma G] (h : Equation35110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation35111_implies_Equation2 (G : Type*) [Magma G] (h : Equation35111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation35113_implies_Equation2 (G : Type*) [Magma G] (h : Equation35113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq9 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq13
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq79 eq33


@[equational_result]
theorem Equation35114_implies_Equation2 (G : Type*) [Magma G] (h : Equation35114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ ((X1 ◇ X1) ◇ X3)) ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X1) ◇ X3)) ◇ ((X2 ◇ X2) ◇ X1))) ◇ X0)) = X3 := superpose eq9 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq13 eq9
  have eq40 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq21 eq21
  have eq81 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq40 eq7
  have eq120 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq40 eq81
  have eq163 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq120 eq40
  have eq166 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq120 eq81
  have eq291 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq120 eq163
  have eq297 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq291 eq166
  have eq315 (X0 X2 : G) : X0 = X2 := superpose eq297 eq297
  have eq343 (X0 : G) : sK0 ≠ X0 := superpose eq315 eq8
  subsumption eq343 eq315


@[equational_result]
theorem Equation35115_implies_Equation2 (G : Type*) [Magma G] (h : Equation35115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq41 eq14


@[equational_result]
theorem Equation35117_implies_Equation2 (G : Type*) [Magma G] (h : Equation35117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35118_implies_Equation2 (G : Type*) [Magma G] (h : Equation35118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35119_implies_Equation2 (G : Type*) [Magma G] (h : Equation35119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35121_implies_Equation2 (G : Type*) [Magma G] (h : Equation35121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35122_implies_Equation2 (G : Type*) [Magma G] (h : Equation35122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35123_implies_Equation2 (G : Type*) [Magma G] (h : Equation35123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35125_implies_Equation2 (G : Type*) [Magma G] (h : Equation35125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35126_implies_Equation2 (G : Type*) [Magma G] (h : Equation35126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35127_implies_Equation2 (G : Type*) [Magma G] (h : Equation35127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35128_implies_Equation2 (G : Type*) [Magma G] (h : Equation35128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35130_implies_Equation2 (G : Type*) [Magma G] (h : Equation35130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq9
  have eq28 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq10
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq28 eq14
  have eq55 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq28 eq50
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq55 eq55
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq68 eq56


@[equational_result]
theorem Equation35131_implies_Equation2 (G : Type*) [Magma G] (h : Equation35131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq10
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq32 eq25


@[equational_result]
theorem Equation35132_implies_Equation2 (G : Type*) [Magma G] (h : Equation35132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq38 eq13


@[equational_result]
theorem Equation35134_implies_Equation2 (G : Type*) [Magma G] (h : Equation35134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35135_implies_Equation2 (G : Type*) [Magma G] (h : Equation35135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35136_implies_Equation2 (G : Type*) [Magma G] (h : Equation35136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35138_implies_Equation2 (G : Type*) [Magma G] (h : Equation35138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35139_implies_Equation2 (G : Type*) [Magma G] (h : Equation35139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation35140_implies_Equation2 (G : Type*) [Magma G] (h : Equation35140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35142_implies_Equation2 (G : Type*) [Magma G] (h : Equation35142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35143_implies_Equation2 (G : Type*) [Magma G] (h : Equation35143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35144_implies_Equation2 (G : Type*) [Magma G] (h : Equation35144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation35145_implies_Equation2 (G : Type*) [Magma G] (h : Equation35145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35147_implies_Equation2 (G : Type*) [Magma G] (h : Equation35147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq40 eq18


@[equational_result]
theorem Equation35148_implies_Equation2 (G : Type*) [Magma G] (h : Equation35148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation35149_implies_Equation2 (G : Type*) [Magma G] (h : Equation35149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation35150_implies_Equation2 (G : Type*) [Magma G] (h : Equation35150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation35152_implies_Equation2 (G : Type*) [Magma G] (h : Equation35152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35153_implies_Equation2 (G : Type*) [Magma G] (h : Equation35153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35154_implies_Equation2 (G : Type*) [Magma G] (h : Equation35154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35155_implies_Equation2 (G : Type*) [Magma G] (h : Equation35155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35157_implies_Equation2 (G : Type*) [Magma G] (h : Equation35157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35158_implies_Equation2 (G : Type*) [Magma G] (h : Equation35158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35159_implies_Equation2 (G : Type*) [Magma G] (h : Equation35159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35160_implies_Equation2 (G : Type*) [Magma G] (h : Equation35160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35162_implies_Equation2 (G : Type*) [Magma G] (h : Equation35162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35163_implies_Equation2 (G : Type*) [Magma G] (h : Equation35163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35164_implies_Equation2 (G : Type*) [Magma G] (h : Equation35164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35165_implies_Equation2 (G : Type*) [Magma G] (h : Equation35165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35167_implies_Equation2 (G : Type*) [Magma G] (h : Equation35167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35168_implies_Equation2 (G : Type*) [Magma G] (h : Equation35168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation35169_implies_Equation2 (G : Type*) [Magma G] (h : Equation35169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35170_implies_Equation2 (G : Type*) [Magma G] (h : Equation35170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35171_implies_Equation2 (G : Type*) [Magma G] (h : Equation35171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35173_implies_Equation2 (G : Type*) [Magma G] (h : Equation35173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X3) ◇ X3)) ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X0))) ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := superpose eq12 eq9
  have eq56 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X3)) ◇ X0)) ◇ (((X3 ◇ X0) ◇ X0) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq10
  have eq63 (X0 X1 X2 : G) : (((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1) ◇ X0) = ((X0 ◇ (X2 ◇ (((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1) ◇ X0))) ◇ X1) := superpose eq12 eq10
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1) ◇ X0) := superpose eq12 eq63
  have eq84 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq83 eq12
  have eq95 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq84 eq25
  have eq127 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X0) ◇ X0) ◇ X2)) ◇ X1) = X2 := superpose eq95 eq56
  have eq137 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ X0)) ◇ X1) = X2 := superpose eq95 eq127
  have eq138 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq95 eq137
  have eq144 (X0 X1 : G) : X0 = X1 := superpose eq95 eq138
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq149 eq144


@[equational_result]
theorem Equation35174_implies_Equation2 (G : Type*) [Magma G] (h : Equation35174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq109 eq32


@[equational_result]
theorem Equation35175_implies_Equation2 (G : Type*) [Magma G] (h : Equation35175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35179_implies_Equation2 (G : Type*) [Magma G] (h : Equation35179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq47 eq13


@[equational_result]
theorem Equation35182_implies_Equation2 (G : Type*) [Magma G] (h : Equation35182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq124 eq33


@[equational_result]
theorem Equation35183_implies_Equation2 (G : Type*) [Magma G] (h : Equation35183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation35185_implies_Equation2 (G : Type*) [Magma G] (h : Equation35185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X4))) ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X1)) = X3 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ X4) ◇ X5) = ((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (((X6 ◇ X3) ◇ (X7 ◇ X0)) ◇ X1)) := superpose eq11 eq11
  have eq48 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (((X0 ◇ X6) ◇ X7) ◇ X2)) = X6 := superpose eq12 eq12
  have eq67 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ X5) = X3 := superpose eq48 eq23
  have eq90 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq67 eq10
  have eq104 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq67 eq90
  have eq109 (X0 X2 : G) : X0 = X2 := superpose eq104 eq104
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq119 eq109


@[equational_result]
theorem Equation35186_implies_Equation2 (G : Type*) [Magma G] (h : Equation35186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ ((X2 ◇ X4) ◇ X5)) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq158 eq59


@[equational_result]
theorem Equation35187_implies_Equation2 (G : Type*) [Magma G] (h : Equation35187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq124 eq41


@[equational_result]
theorem Equation35188_implies_Equation2 (G : Type*) [Magma G] (h : Equation35188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X4))) ◇ (X0 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X3 X5 X7 : G) : (X3 ◇ X7) = X5 := superpose eq9 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation35191_implies_Equation2 (G : Type*) [Magma G] (h : Equation35191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X0))) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3) ◇ X0) ◇ X3) ◇ X0) = X1 := superpose eq7 eq11
  have eq49 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X3 ◇ ((X4 ◇ X3) ◇ ((X3 ◇ X4) ◇ (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)))))) ◇ X0)) ◇ X3) = X1 := superpose eq9 eq16
  have eq79 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq11
  have eq93 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq79 eq49
  have eq95 (X0 X3 : G) : X0 = X3 := superpose eq7 eq93
  have eq209 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq209 eq95


@[equational_result]
theorem Equation35192_implies_Equation2 (G : Type*) [Magma G] (h : Equation35192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation35194_implies_Equation2 (G : Type*) [Magma G] (h : Equation35194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35195_implies_Equation2 (G : Type*) [Magma G] (h : Equation35195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35196_implies_Equation2 (G : Type*) [Magma G] (h : Equation35196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation35198_implies_Equation2 (G : Type*) [Magma G] (h : Equation35198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation35199_implies_Equation2 (G : Type*) [Magma G] (h : Equation35199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


