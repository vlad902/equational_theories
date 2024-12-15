import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation29632_implies_Equation2 (G : Type*) [Magma G] (h : Equation29632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29636_implies_Equation2 (G : Type*) [Magma G] (h : Equation29636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29638_implies_Equation2 (G : Type*) [Magma G] (h : Equation29638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5)))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 X6 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X6 ◇ (X6 ◇ (X2 ◇ X3))) ◇ X6) := superpose eq10 eq10
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ (X1 ◇ (X6 ◇ X7))) ◇ (X8 ◇ X9)))) = (((X4 ◇ X5) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X4 ◇ X5)) := superpose eq10 eq10
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ ((X1 ◇ (X4 ◇ X5)) ◇ (X6 ◇ X7)))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X8 ◇ X9)) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6)))) = X0 := superpose eq7 eq10
  have eq58 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := superpose eq9 eq34
  have eq60 (X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ (X1 ◇ (X6 ◇ X7))) ◇ (X8 ◇ X9)))) = (X4 ◇ (X4 ◇ X5)) := superpose eq58 eq39
  have eq61 (X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ (X4 ◇ X5)) := superpose eq41 eq60
  have eq62 (X0 X1 X8 X9 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X8 ◇ X9)) = X1 := superpose eq41 eq40
  have eq77 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq61 eq9
  have eq92 (X0 X1 X8 X9 : G) : (X0 ◇ (X8 ◇ X9)) = X1 := superpose eq77 eq62
  have eq99 (X0 X4 : G) : X0 = X4 := superpose eq92 eq92
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq114 eq99


@[equational_result]
theorem Equation29639_implies_Equation2 (G : Type*) [Magma G] (h : Equation29639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X5))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X6 ◇ (X6 ◇ ((X3 ◇ (X2 ◇ (X4 ◇ X5))) ◇ (X7 ◇ X8))))) = X3 := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X4)))))) ◇ (X5 ◇ (X5 ◇ X0))) = X2 := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq9 eq7
  have eq32 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X2) = X0 := superpose eq26 eq7
  have eq35 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ (X5 ◇ (X5 ◇ X0))) = X2 := superpose eq26 eq20
  have eq37 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X0) ◇ X3) = X2 := superpose eq26 eq11
  have eq38 (X0 X2 X3 X4 X5 X6 X7 X8 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X6 ◇ (X6 ◇ ((X3 ◇ (X2 ◇ (X4 ◇ X5))) ◇ (X7 ◇ X8))))) = X3 := superpose eq26 eq15
  have eq47 (X0 X2 X4 X5 : G) : ((X2 ◇ (X0 ◇ X4)) ◇ (X5 ◇ (X5 ◇ X0))) = X2 := superpose eq26 eq35
  have eq49 (X0 X2 X3 X4 X5 X7 X8 : G) : (((X0 ◇ X2) ◇ X0) ◇ ((X3 ◇ (X2 ◇ (X4 ◇ X5))) ◇ (X7 ◇ X8))) = X3 := superpose eq26 eq38
  have eq56 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq32 eq32
  have eq60 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = X2 := superpose eq56 eq37
  have eq62 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X1 := superpose eq32 eq60
  have eq70 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X1 := superpose eq26 eq62
  have eq71 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ X3) = X3 := superpose eq70 eq49
  have eq76 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq70 eq71
  have eq77 (X0 X2 X4 X5 : G) : ((X2 ◇ (X0 ◇ X4)) ◇ (X5 ◇ X0)) = X2 := superpose eq76 eq47
  have eq84 (X0 X2 X4 : G) : ((X2 ◇ (X0 ◇ X4)) ◇ X0) = X2 := superpose eq76 eq77
  have eq85 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X0) = X2 := superpose eq76 eq84
  have eq86 (X0 X2 X4 : G) : (X4 ◇ X0) = X2 := superpose eq76 eq85
  have eq87 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq92 eq87


@[equational_result]
theorem Equation29640_implies_Equation2 (G : Type*) [Magma G] (h : Equation29640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X5) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq9 eq11
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation29641_implies_Equation2 (G : Type*) [Magma G] (h : Equation29641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X7 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X0) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29644_implies_Equation2 (G : Type*) [Magma G] (h : Equation29644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq75 eq14


@[equational_result]
theorem Equation29647_implies_Equation2 (G : Type*) [Magma G] (h : Equation29647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq75 eq14


@[equational_result]
theorem Equation29649_implies_Equation2 (G : Type*) [Magma G] (h : Equation29649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) ◇ X2) = X3 := superpose eq9 eq7
  have eq36 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq24 eq29
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq151 eq58


@[equational_result]
theorem Equation29651_implies_Equation2 (G : Type*) [Magma G] (h : Equation29651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation29654_implies_Equation2 (G : Type*) [Magma G] (h : Equation29654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29656_implies_Equation2 (G : Type*) [Magma G] (h : Equation29656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation29657_implies_Equation2 (G : Type*) [Magma G] (h : Equation29657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29659_implies_Equation2 (G : Type*) [Magma G] (h : Equation29659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29660_implies_Equation2 (G : Type*) [Magma G] (h : Equation29660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29661_implies_Equation2 (G : Type*) [Magma G] (h : Equation29661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29663_implies_Equation2 (G : Type*) [Magma G] (h : Equation29663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation29665_implies_Equation2 (G : Type*) [Magma G] (h : Equation29665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation29667_implies_Equation2 (G : Type*) [Magma G] (h : Equation29667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29668_implies_Equation2 (G : Type*) [Magma G] (h : Equation29668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29669_implies_Equation2 (G : Type*) [Magma G] (h : Equation29669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29671_implies_Equation2 (G : Type*) [Magma G] (h : Equation29671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29672_implies_Equation2 (G : Type*) [Magma G] (h : Equation29672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29673_implies_Equation2 (G : Type*) [Magma G] (h : Equation29673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29675_implies_Equation2 (G : Type*) [Magma G] (h : Equation29675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29676_implies_Equation2 (G : Type*) [Magma G] (h : Equation29676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29677_implies_Equation2 (G : Type*) [Magma G] (h : Equation29677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29678_implies_Equation2 (G : Type*) [Magma G] (h : Equation29678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29680_implies_Equation2 (G : Type*) [Magma G] (h : Equation29680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation29682_implies_Equation2 (G : Type*) [Magma G] (h : Equation29682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation29684_implies_Equation2 (G : Type*) [Magma G] (h : Equation29684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation29686_implies_Equation2 (G : Type*) [Magma G] (h : Equation29686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation29690_implies_Equation2 (G : Type*) [Magma G] (h : Equation29690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation29692_implies_Equation2 (G : Type*) [Magma G] (h : Equation29692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation29693_implies_Equation2 (G : Type*) [Magma G] (h : Equation29693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X5)))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X3 ◇ (X4 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)))) ◇ X4) = X5 := superpose eq9 eq7
  have eq41 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq29 eq34
  have eq78 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq185 eq78


@[equational_result]
theorem Equation29694_implies_Equation2 (G : Type*) [Magma G] (h : Equation29694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq83 eq17


@[equational_result]
theorem Equation29695_implies_Equation2 (G : Type*) [Magma G] (h : Equation29695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 X7 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X0) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation29697_implies_Equation2 (G : Type*) [Magma G] (h : Equation29697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation29699_implies_Equation2 (G : Type*) [Magma G] (h : Equation29699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29701_implies_Equation2 (G : Type*) [Magma G] (h : Equation29701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29702_implies_Equation2 (G : Type*) [Magma G] (h : Equation29702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29703_implies_Equation2 (G : Type*) [Magma G] (h : Equation29703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29705_implies_Equation2 (G : Type*) [Magma G] (h : Equation29705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29706_implies_Equation2 (G : Type*) [Magma G] (h : Equation29706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29707_implies_Equation2 (G : Type*) [Magma G] (h : Equation29707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29709_implies_Equation2 (G : Type*) [Magma G] (h : Equation29709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29710_implies_Equation2 (G : Type*) [Magma G] (h : Equation29710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29711_implies_Equation2 (G : Type*) [Magma G] (h : Equation29711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29712_implies_Equation2 (G : Type*) [Magma G] (h : Equation29712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29714_implies_Equation2 (G : Type*) [Magma G] (h : Equation29714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq7 eq9
  have eq37 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X0 := superpose eq7 eq15
  have eq69 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq37 eq7
  have eq100 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq37 eq69
  have eq101 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq100 eq37
  have eq135 (X0 X1 : G) : X0 = X1 := superpose eq100 eq101
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq135 eq8
  subsumption eq149 eq135


@[equational_result]
theorem Equation29715_implies_Equation2 (G : Type*) [Magma G] (h : Equation29715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X0))) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)))) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X0) ◇ (((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X0) ◇ X4)))) ◇ X4) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0))))) = X3 := superpose eq7 eq10
  have eq16 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq7 eq9
  have eq37 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq16
  have eq52 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X4)) ◇ X4) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0))))) = X3 := superpose eq37 eq11
  have eq63 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq37 eq19
  have eq79 (X0 X1 X3 X4 : G) : (((X1 ◇ (X1 ◇ X4)) ◇ X4) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq37 eq52
  have eq80 (X0 X1 X3 X4 : G) : (((X1 ◇ (X1 ◇ X4)) ◇ X4) ◇ X0) = X3 := superpose eq37 eq79
  have eq81 (X0 X3 X4 : G) : ((X4 ◇ X4) ◇ X0) = X3 := superpose eq37 eq80
  have eq105 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq37 eq63
  have eq106 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq105
  have eq108 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq106 eq81
  have eq110 (X0 X1 : G) : X0 = X1 := superpose eq106 eq108
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq110 eq8
  subsumption eq134 eq110


@[equational_result]
theorem Equation29716_implies_Equation2 (G : Type*) [Magma G] (h : Equation29716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation29718_implies_Equation2 (G : Type*) [Magma G] (h : Equation29718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29719_implies_Equation2 (G : Type*) [Magma G] (h : Equation29719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29720_implies_Equation2 (G : Type*) [Magma G] (h : Equation29720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29722_implies_Equation2 (G : Type*) [Magma G] (h : Equation29722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29723_implies_Equation2 (G : Type*) [Magma G] (h : Equation29723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29724_implies_Equation2 (G : Type*) [Magma G] (h : Equation29724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29726_implies_Equation2 (G : Type*) [Magma G] (h : Equation29726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29727_implies_Equation2 (G : Type*) [Magma G] (h : Equation29727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29728_implies_Equation2 (G : Type*) [Magma G] (h : Equation29728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29729_implies_Equation2 (G : Type*) [Magma G] (h : Equation29729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29731_implies_Equation2 (G : Type*) [Magma G] (h : Equation29731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation29732_implies_Equation2 (G : Type*) [Magma G] (h : Equation29732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation29733_implies_Equation2 (G : Type*) [Magma G] (h : Equation29733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = X5 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq65 eq17


@[equational_result]
theorem Equation29734_implies_Equation2 (G : Type*) [Magma G] (h : Equation29734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X6 X7 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X0) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation29736_implies_Equation2 (G : Type*) [Magma G] (h : Equation29736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29737_implies_Equation2 (G : Type*) [Magma G] (h : Equation29737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29738_implies_Equation2 (G : Type*) [Magma G] (h : Equation29738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29739_implies_Equation2 (G : Type*) [Magma G] (h : Equation29739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29741_implies_Equation2 (G : Type*) [Magma G] (h : Equation29741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29742_implies_Equation2 (G : Type*) [Magma G] (h : Equation29742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29743_implies_Equation2 (G : Type*) [Magma G] (h : Equation29743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29744_implies_Equation2 (G : Type*) [Magma G] (h : Equation29744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29746_implies_Equation2 (G : Type*) [Magma G] (h : Equation29746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29747_implies_Equation2 (G : Type*) [Magma G] (h : Equation29747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29748_implies_Equation2 (G : Type*) [Magma G] (h : Equation29748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29749_implies_Equation2 (G : Type*) [Magma G] (h : Equation29749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29751_implies_Equation2 (G : Type*) [Magma G] (h : Equation29751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29752_implies_Equation2 (G : Type*) [Magma G] (h : Equation29752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29753_implies_Equation2 (G : Type*) [Magma G] (h : Equation29753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29754_implies_Equation2 (G : Type*) [Magma G] (h : Equation29754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29755_implies_Equation2 (G : Type*) [Magma G] (h : Equation29755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29757_implies_Equation2 (G : Type*) [Magma G] (h : Equation29757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq39 eq14


@[equational_result]
theorem Equation29758_implies_Equation2 (G : Type*) [Magma G] (h : Equation29758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation29759_implies_Equation2 (G : Type*) [Magma G] (h : Equation29759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29761_implies_Equation2 (G : Type*) [Magma G] (h : Equation29761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29763_implies_Equation2 (G : Type*) [Magma G] (h : Equation29763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29766_implies_Equation2 (G : Type*) [Magma G] (h : Equation29766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation29767_implies_Equation2 (G : Type*) [Magma G] (h : Equation29767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29769_implies_Equation2 (G : Type*) [Magma G] (h : Equation29769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation29770_implies_Equation2 (G : Type*) [Magma G] (h : Equation29770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation29771_implies_Equation2 (G : Type*) [Magma G] (h : Equation29771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation29772_implies_Equation2 (G : Type*) [Magma G] (h : Equation29772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29774_implies_Equation2 (G : Type*) [Magma G] (h : Equation29774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation29776_implies_Equation2 (G : Type*) [Magma G] (h : Equation29776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29778_implies_Equation2 (G : Type*) [Magma G] (h : Equation29778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation29780_implies_Equation2 (G : Type*) [Magma G] (h : Equation29780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29784_implies_Equation2 (G : Type*) [Magma G] (h : Equation29784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29786_implies_Equation2 (G : Type*) [Magma G] (h : Equation29786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation29787_implies_Equation2 (G : Type*) [Magma G] (h : Equation29787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ X0))) ◇ X4) = X5 := superpose eq7 eq7
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq75 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq185 eq75


@[equational_result]
theorem Equation29788_implies_Equation2 (G : Type*) [Magma G] (h : Equation29788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation29789_implies_Equation2 (G : Type*) [Magma G] (h : Equation29789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X7 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ X0))) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29791_implies_Equation2 (G : Type*) [Magma G] (h : Equation29791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X0 ◇ (X4 ◇ X0)))) = ((X1 ◇ (X0 ◇ (((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X0 ◇ (X4 ◇ X0)))) ◇ X3))) ◇ X1) := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ (((X4 ◇ (X0 ◇ (X4 ◇ X0))) ◇ (X5 ◇ (X2 ◇ (X5 ◇ X2)))) ◇ (X3 ◇ ((X4 ◇ (X0 ◇ (X4 ◇ X0))) ◇ (X5 ◇ (X2 ◇ (X5 ◇ X2)))))))) ◇ X0)) ◇ X1) = X2 := superpose eq10 eq9
  have eq1108 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ X3) = X1 := superpose eq7 eq27
  have eq1213 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ ((X4 ◇ (X0 ◇ (X4 ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0)))))) = X2 := superpose eq1108 eq1108
  have eq1214 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq1108
  have eq1407 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq1214 eq9
  have eq1513 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq1214 eq1407
  have eq1514 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq1214 eq1513
  have eq1515 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq1214 eq1514
  have eq1520 (X0 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X0 ◇ (X4 ◇ X0)))) = X0 := superpose eq1515 eq13
  have eq1605 (X0 X2 X4 X5 : G) : (X0 ◇ (X2 ◇ ((X4 ◇ (X0 ◇ (X4 ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0)))))) = X2 := superpose eq1520 eq1213
  have eq1937 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq1520 eq1605
  have eq2012 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X1) = X0 := superpose eq1937 eq7
  have eq2446 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq1214 eq2012
  have eq2519 (X0 X3 : G) : X0 = X3 := superpose eq2446 eq2446
  have eq2523 (X0 : G) : sK0 ≠ X0 := superpose eq2519 eq8
  subsumption eq2523 eq2519


@[equational_result]
theorem Equation29792_implies_Equation2 (G : Type*) [Magma G] (h : Equation29792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq45 eq11


@[equational_result]
theorem Equation29793_implies_Equation2 (G : Type*) [Magma G] (h : Equation29793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29797_implies_Equation2 (G : Type*) [Magma G] (h : Equation29797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29800_implies_Equation2 (G : Type*) [Magma G] (h : Equation29800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq65 eq11


@[equational_result]
theorem Equation29801_implies_Equation2 (G : Type*) [Magma G] (h : Equation29801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29803_implies_Equation2 (G : Type*) [Magma G] (h : Equation29803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ (X5 ◇ X0))) ◇ X1) = X5 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq85 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq191 eq85


@[equational_result]
theorem Equation29804_implies_Equation2 (G : Type*) [Magma G] (h : Equation29804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation29805_implies_Equation2 (G : Type*) [Magma G] (h : Equation29805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation29806_implies_Equation2 (G : Type*) [Magma G] (h : Equation29806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29808_implies_Equation2 (G : Type*) [Magma G] (h : Equation29808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation29809_implies_Equation2 (G : Type*) [Magma G] (h : Equation29809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation29810_implies_Equation2 (G : Type*) [Magma G] (h : Equation29810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation29811_implies_Equation2 (G : Type*) [Magma G] (h : Equation29811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29813_implies_Equation2 (G : Type*) [Magma G] (h : Equation29813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation29814_implies_Equation2 (G : Type*) [Magma G] (h : Equation29814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq9
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq168 eq64


@[equational_result]
theorem Equation29815_implies_Equation2 (G : Type*) [Magma G] (h : Equation29815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq63 eq15


@[equational_result]
theorem Equation29816_implies_Equation2 (G : Type*) [Magma G] (h : Equation29816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29818_implies_Equation2 (G : Type*) [Magma G] (h : Equation29818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq74 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq166 eq74


@[equational_result]
theorem Equation29819_implies_Equation2 (G : Type*) [Magma G] (h : Equation29819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation29820_implies_Equation2 (G : Type*) [Magma G] (h : Equation29820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation29821_implies_Equation2 (G : Type*) [Magma G] (h : Equation29821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29823_implies_Equation2 (G : Type*) [Magma G] (h : Equation29823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation29824_implies_Equation2 (G : Type*) [Magma G] (h : Equation29824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq72 eq12


@[equational_result]
theorem Equation29825_implies_Equation2 (G : Type*) [Magma G] (h : Equation29825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation29826_implies_Equation2 (G : Type*) [Magma G] (h : Equation29826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29828_implies_Equation2 (G : Type*) [Magma G] (h : Equation29828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation29829_implies_Equation2 (G : Type*) [Magma G] (h : Equation29829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation29830_implies_Equation2 (G : Type*) [Magma G] (h : Equation29830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29831_implies_Equation2 (G : Type*) [Magma G] (h : Equation29831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29832_implies_Equation2 (G : Type*) [Magma G] (h : Equation29832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X9 : G) : (X0 ◇ X9) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29834_implies_Equation2 (G : Type*) [Magma G] (h : Equation29834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29836_implies_Equation2 (G : Type*) [Magma G] (h : Equation29836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation29838_implies_Equation2 (G : Type*) [Magma G] (h : Equation29838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq63 eq14


@[equational_result]
theorem Equation29840_implies_Equation2 (G : Type*) [Magma G] (h : Equation29840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation29844_implies_Equation2 (G : Type*) [Magma G] (h : Equation29844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation29846_implies_Equation2 (G : Type*) [Magma G] (h : Equation29846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation29847_implies_Equation2 (G : Type*) [Magma G] (h : Equation29847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X5)))) = ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)))) ◇ X4) = X5 := superpose eq9 eq7
  have eq41 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq29 eq34
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq188 eq73


@[equational_result]
theorem Equation29848_implies_Equation2 (G : Type*) [Magma G] (h : Equation29848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq79 eq15


@[equational_result]
theorem Equation29849_implies_Equation2 (G : Type*) [Magma G] (h : Equation29849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X7 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ (X4 ◇ X0)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation29851_implies_Equation2 (G : Type*) [Magma G] (h : Equation29851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq48 eq14


@[equational_result]
theorem Equation29853_implies_Equation2 (G : Type*) [Magma G] (h : Equation29853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29855_implies_Equation2 (G : Type*) [Magma G] (h : Equation29855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29856_implies_Equation2 (G : Type*) [Magma G] (h : Equation29856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29857_implies_Equation2 (G : Type*) [Magma G] (h : Equation29857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29859_implies_Equation2 (G : Type*) [Magma G] (h : Equation29859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29860_implies_Equation2 (G : Type*) [Magma G] (h : Equation29860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29861_implies_Equation2 (G : Type*) [Magma G] (h : Equation29861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29863_implies_Equation2 (G : Type*) [Magma G] (h : Equation29863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29864_implies_Equation2 (G : Type*) [Magma G] (h : Equation29864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29865_implies_Equation2 (G : Type*) [Magma G] (h : Equation29865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29866_implies_Equation2 (G : Type*) [Magma G] (h : Equation29866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29868_implies_Equation2 (G : Type*) [Magma G] (h : Equation29868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ (X1 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)))) = ((X1 ◇ ((((X2 ◇ X3) ◇ (X4 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0)))) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3))) ◇ X1) := superpose eq7 eq9
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq7 eq17
  have eq60 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3))) ◇ X1) = X0 := superpose eq42 eq13
  have eq73 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq42 eq7
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) = X0 := superpose eq73 eq60
  have eq94 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq73 eq87
  have eq96 (X0 X1 : G) : X0 = X1 := superpose eq73 eq94
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq104 eq96


@[equational_result]
theorem Equation29869_implies_Equation2 (G : Type*) [Magma G] (h : Equation29869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) ◇ (X2 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((((X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X1 ◇ ((((X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) ◇ (X3 ◇ X4)) ◇ X5) ◇ X3)))) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) ◇ (X3 ◇ X4))) = X5 := superpose eq10 eq10
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X5) ◇ (X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X5) ◇ X3)))) ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X4))) = X5 := superpose eq19 eq18
  have eq33 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X5) ◇ (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X5) ◇ X3)))) ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) = X5 := superpose eq19 eq22
  have eq34 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X2 ◇ X5) ◇ (X1 ◇ ((X2 ◇ X5) ◇ X3)))) ◇ X0) ◇ X2) = X5 := superpose eq19 eq33
  have eq35 (X1 X2 X3 X5 : G) : ((X1 ◇ ((X2 ◇ X5) ◇ (X1 ◇ ((X2 ◇ X5) ◇ X3)))) ◇ X2) = X5 := superpose eq19 eq34
  have eq36 (X1 X2 X5 : G) : (X1 ◇ X2) = X5 := superpose eq19 eq35
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq42 eq37


@[equational_result]
theorem Equation29870_implies_Equation2 (G : Type*) [Magma G] (h : Equation29870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29872_implies_Equation2 (G : Type*) [Magma G] (h : Equation29872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29873_implies_Equation2 (G : Type*) [Magma G] (h : Equation29873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29874_implies_Equation2 (G : Type*) [Magma G] (h : Equation29874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29876_implies_Equation2 (G : Type*) [Magma G] (h : Equation29876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29877_implies_Equation2 (G : Type*) [Magma G] (h : Equation29877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29878_implies_Equation2 (G : Type*) [Magma G] (h : Equation29878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29880_implies_Equation2 (G : Type*) [Magma G] (h : Equation29880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29881_implies_Equation2 (G : Type*) [Magma G] (h : Equation29881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29882_implies_Equation2 (G : Type*) [Magma G] (h : Equation29882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29883_implies_Equation2 (G : Type*) [Magma G] (h : Equation29883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29885_implies_Equation2 (G : Type*) [Magma G] (h : Equation29885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation29886_implies_Equation2 (G : Type*) [Magma G] (h : Equation29886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation29887_implies_Equation2 (G : Type*) [Magma G] (h : Equation29887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation29888_implies_Equation2 (G : Type*) [Magma G] (h : Equation29888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ (X4 ◇ X0)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation29890_implies_Equation2 (G : Type*) [Magma G] (h : Equation29890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29891_implies_Equation2 (G : Type*) [Magma G] (h : Equation29891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29892_implies_Equation2 (G : Type*) [Magma G] (h : Equation29892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29893_implies_Equation2 (G : Type*) [Magma G] (h : Equation29893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29895_implies_Equation2 (G : Type*) [Magma G] (h : Equation29895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29896_implies_Equation2 (G : Type*) [Magma G] (h : Equation29896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29897_implies_Equation2 (G : Type*) [Magma G] (h : Equation29897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29898_implies_Equation2 (G : Type*) [Magma G] (h : Equation29898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29900_implies_Equation2 (G : Type*) [Magma G] (h : Equation29900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29901_implies_Equation2 (G : Type*) [Magma G] (h : Equation29901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29902_implies_Equation2 (G : Type*) [Magma G] (h : Equation29902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29903_implies_Equation2 (G : Type*) [Magma G] (h : Equation29903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29905_implies_Equation2 (G : Type*) [Magma G] (h : Equation29905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29906_implies_Equation2 (G : Type*) [Magma G] (h : Equation29906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29907_implies_Equation2 (G : Type*) [Magma G] (h : Equation29907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29908_implies_Equation2 (G : Type*) [Magma G] (h : Equation29908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29909_implies_Equation2 (G : Type*) [Magma G] (h : Equation29909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29912_implies_Equation2 (G : Type*) [Magma G] (h : Equation29912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation29913_implies_Equation2 (G : Type*) [Magma G] (h : Equation29913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29917_implies_Equation2 (G : Type*) [Magma G] (h : Equation29917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29919_implies_Equation2 (G : Type*) [Magma G] (h : Equation29919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) = ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) = ((X4 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X4) := superpose eq9 eq9
  have eq19 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)))) = ((X4 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X4) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) = (X0 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X4))))) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X4 ◇ ((X2 ◇ X3) ◇ X4)))) = (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X1) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X1) = X2 := superpose eq23 eq22
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq23
  have eq77 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq23 eq31
  have eq81 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X1)) ◇ X2) = X3 := superpose eq31 eq31
  have eq119 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq54 eq31
  have eq128 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq7 eq119
  have eq152 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((X4 ◇ (X2 ◇ X0)) ◇ X4) := superpose eq23 eq15
  have eq156 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ X1) := superpose eq23 eq15
  have eq217 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq156 eq156
  have eq769 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X1 := superpose eq77 eq23
  have eq1015 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) = ((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X0 ◇ (X0 ◇ X2))))))) ◇ X3) := superpose eq20 eq15
  have eq1101 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq156 eq769
  have eq1118 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) = X2 := superpose eq77 eq769
  have eq1930 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) = (((X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1)) ◇ X0)) ◇ X4) ◇ X2) := superpose eq19 eq31
  have eq3131 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq1101 eq15
  have eq3133 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq1101 eq31
  have eq3591 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq3133 eq152
  have eq3593 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose eq3133 eq1118
  have eq3599 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) := superpose eq3133 eq217
  have eq3605 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) := superpose eq3133 eq769
  have eq3608 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq128 eq3593
  have eq3864 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)) = X1 := superpose eq9 eq3608
  have eq3865 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq10 eq3608
  have eq3901 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) = ((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X4)) ◇ X3) := superpose eq3865 eq1015
  have eq3906 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq3865 eq3591
  have eq3912 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ X0) := superpose eq3865 eq3605
  have eq5126 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = ((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X4)) ◇ X3) := superpose eq3865 eq3901
  have eq5128 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X2) = X3 := superpose eq5126 eq81
  have eq5138 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq3906 eq3599
  have eq5139 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq5138 eq3864
  have eq5140 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) = X0 := superpose eq5139 eq3131
  have eq5142 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ X0) := superpose eq5139 eq5138
  have eq5143 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq5142 eq5140
  have eq5144 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq3865 eq3912
  have eq5147 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq5144 eq5143
  have eq5157 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq5144 eq5147
  have eq5159 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X2)) = (((X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1)) ◇ X0)) ◇ X4) ◇ X2) := superpose eq5157 eq1930
  have eq5265 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (((X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1)) ◇ X0) ◇ X2) := superpose eq5157 eq5159
  have eq5266 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) ◇ X2) := superpose eq5157 eq5265
  have eq5267 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X2 ◇ (X2 ◇ X3)) ◇ X2) := superpose eq5157 eq5266
  have eq5268 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X2 ◇ X3) := superpose eq5157 eq5267
  have eq5270 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq5268 eq3865
  have eq5274 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = ((X3 ◇ (X2 ◇ X4)) ◇ X3) := superpose eq5270 eq5126
  have eq5275 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq5270 eq5128
  have eq5277 (X0 X2 X4 : G) : (X2 ◇ X4) = ((X0 ◇ X2) ◇ X4) := superpose eq5157 eq5274
  have eq5278 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2) = X3 := superpose eq5277 eq5275
  have eq5279 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = X3 := superpose eq5270 eq5278
  have eq5280 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq5144 eq5279
  have eq5281 (X0 X3 : G) : X0 = X3 := superpose eq5280 eq5280
  have eq5283 (X0 : G) : sK0 ≠ X0 := superpose eq5281 eq8
  subsumption eq5283 eq5281


@[equational_result]
theorem Equation29920_implies_Equation2 (G : Type*) [Magma G] (h : Equation29920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq66 eq11


@[equational_result]
theorem Equation29921_implies_Equation2 (G : Type*) [Magma G] (h : Equation29921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29923_implies_Equation2 (G : Type*) [Magma G] (h : Equation29923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X5)))) = ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X5)))) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ (X4 ◇ (X4 ◇ ((X2 ◇ X5) ◇ X6)))) = (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X7) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := superpose eq7 eq9
  have eq41 (X0 X1 X2 X7 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X7) = X2 := superpose eq29 eq28
  have eq45 (X0 X1 X2 X3 X4 X7 X8 X9 : G) : ((X3 ◇ ((((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X7 ◇ (X7 ◇ (X8 ◇ X9)))) ◇ X8)) ◇ X3) = X4 := superpose eq9 eq10
  have eq74 (X2 X3 X4 X8 : G) : ((X3 ◇ (X2 ◇ X8)) ◇ X3) = X4 := superpose eq41 eq45
  have eq87 (X0 X4 : G) : X0 = X4 := superpose eq7 eq74
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq193 eq87


@[equational_result]
theorem Equation29924_implies_Equation2 (G : Type*) [Magma G] (h : Equation29924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq72 eq12


@[equational_result]
theorem Equation29925_implies_Equation2 (G : Type*) [Magma G] (h : Equation29925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq75 eq12


@[equational_result]
theorem Equation29926_implies_Equation2 (G : Type*) [Magma G] (h : Equation29926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29928_implies_Equation2 (G : Type*) [Magma G] (h : Equation29928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq10
  have eq39 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq17
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq39 eq17
  have eq87 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq56 eq39
  have eq153 (X0 X1 : G) : X0 = X1 := superpose eq56 eq87
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq153 eq8
  subsumption eq172 eq153


@[equational_result]
theorem Equation29930_implies_Equation2 (G : Type*) [Magma G] (h : Equation29930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29932_implies_Equation2 (G : Type*) [Magma G] (h : Equation29932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29933_implies_Equation2 (G : Type*) [Magma G] (h : Equation29933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29934_implies_Equation2 (G : Type*) [Magma G] (h : Equation29934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29936_implies_Equation2 (G : Type*) [Magma G] (h : Equation29936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29937_implies_Equation2 (G : Type*) [Magma G] (h : Equation29937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29938_implies_Equation2 (G : Type*) [Magma G] (h : Equation29938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29940_implies_Equation2 (G : Type*) [Magma G] (h : Equation29940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29941_implies_Equation2 (G : Type*) [Magma G] (h : Equation29941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29942_implies_Equation2 (G : Type*) [Magma G] (h : Equation29942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29943_implies_Equation2 (G : Type*) [Magma G] (h : Equation29943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29946_implies_Equation2 (G : Type*) [Magma G] (h : Equation29946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation29947_implies_Equation2 (G : Type*) [Magma G] (h : Equation29947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29949_implies_Equation2 (G : Type*) [Magma G] (h : Equation29949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29950_implies_Equation2 (G : Type*) [Magma G] (h : Equation29950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29951_implies_Equation2 (G : Type*) [Magma G] (h : Equation29951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29953_implies_Equation2 (G : Type*) [Magma G] (h : Equation29953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29954_implies_Equation2 (G : Type*) [Magma G] (h : Equation29954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29955_implies_Equation2 (G : Type*) [Magma G] (h : Equation29955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29957_implies_Equation2 (G : Type*) [Magma G] (h : Equation29957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29958_implies_Equation2 (G : Type*) [Magma G] (h : Equation29958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29959_implies_Equation2 (G : Type*) [Magma G] (h : Equation29959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29960_implies_Equation2 (G : Type*) [Magma G] (h : Equation29960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29962_implies_Equation2 (G : Type*) [Magma G] (h : Equation29962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation29963_implies_Equation2 (G : Type*) [Magma G] (h : Equation29963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation29964_implies_Equation2 (G : Type*) [Magma G] (h : Equation29964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation29965_implies_Equation2 (G : Type*) [Magma G] (h : Equation29965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation29967_implies_Equation2 (G : Type*) [Magma G] (h : Equation29967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29968_implies_Equation2 (G : Type*) [Magma G] (h : Equation29968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29969_implies_Equation2 (G : Type*) [Magma G] (h : Equation29969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29970_implies_Equation2 (G : Type*) [Magma G] (h : Equation29970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29972_implies_Equation2 (G : Type*) [Magma G] (h : Equation29972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29973_implies_Equation2 (G : Type*) [Magma G] (h : Equation29973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29974_implies_Equation2 (G : Type*) [Magma G] (h : Equation29974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29975_implies_Equation2 (G : Type*) [Magma G] (h : Equation29975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29977_implies_Equation2 (G : Type*) [Magma G] (h : Equation29977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29978_implies_Equation2 (G : Type*) [Magma G] (h : Equation29978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29979_implies_Equation2 (G : Type*) [Magma G] (h : Equation29979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29980_implies_Equation2 (G : Type*) [Magma G] (h : Equation29980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29982_implies_Equation2 (G : Type*) [Magma G] (h : Equation29982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29983_implies_Equation2 (G : Type*) [Magma G] (h : Equation29983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29984_implies_Equation2 (G : Type*) [Magma G] (h : Equation29984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29985_implies_Equation2 (G : Type*) [Magma G] (h : Equation29985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29986_implies_Equation2 (G : Type*) [Magma G] (h : Equation29986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29988_implies_Equation2 (G : Type*) [Magma G] (h : Equation29988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation29989_implies_Equation2 (G : Type*) [Magma G] (h : Equation29989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation29990_implies_Equation2 (G : Type*) [Magma G] (h : Equation29990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation29991_implies_Equation2 (G : Type*) [Magma G] (h : Equation29991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29993_implies_Equation2 (G : Type*) [Magma G] (h : Equation29993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation29994_implies_Equation2 (G : Type*) [Magma G] (h : Equation29994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation29995_implies_Equation2 (G : Type*) [Magma G] (h : Equation29995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq77 eq15


@[equational_result]
theorem Equation29996_implies_Equation2 (G : Type*) [Magma G] (h : Equation29996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation29998_implies_Equation2 (G : Type*) [Magma G] (h : Equation29998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq82 eq18


@[equational_result]
theorem Equation29999_implies_Equation2 (G : Type*) [Magma G] (h : Equation29999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30000_implies_Equation2 (G : Type*) [Magma G] (h : Equation30000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation30001_implies_Equation2 (G : Type*) [Magma G] (h : Equation30001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30003_implies_Equation2 (G : Type*) [Magma G] (h : Equation30003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq77 eq15


@[equational_result]
theorem Equation30004_implies_Equation2 (G : Type*) [Magma G] (h : Equation30004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation30005_implies_Equation2 (G : Type*) [Magma G] (h : Equation30005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30006_implies_Equation2 (G : Type*) [Magma G] (h : Equation30006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30008_implies_Equation2 (G : Type*) [Magma G] (h : Equation30008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation30009_implies_Equation2 (G : Type*) [Magma G] (h : Equation30009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30010_implies_Equation2 (G : Type*) [Magma G] (h : Equation30010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30011_implies_Equation2 (G : Type*) [Magma G] (h : Equation30011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30012_implies_Equation2 (G : Type*) [Magma G] (h : Equation30012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X9 : G) : (X0 ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30014_implies_Equation2 (G : Type*) [Magma G] (h : Equation30014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation30015_implies_Equation2 (G : Type*) [Magma G] (h : Equation30015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation30016_implies_Equation2 (G : Type*) [Magma G] (h : Equation30016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation30017_implies_Equation2 (G : Type*) [Magma G] (h : Equation30017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ (X4 ◇ (X5 ◇ X0))) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30019_implies_Equation2 (G : Type*) [Magma G] (h : Equation30019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30020_implies_Equation2 (G : Type*) [Magma G] (h : Equation30020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30021_implies_Equation2 (G : Type*) [Magma G] (h : Equation30021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30022_implies_Equation2 (G : Type*) [Magma G] (h : Equation30022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30024_implies_Equation2 (G : Type*) [Magma G] (h : Equation30024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30025_implies_Equation2 (G : Type*) [Magma G] (h : Equation30025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30026_implies_Equation2 (G : Type*) [Magma G] (h : Equation30026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30027_implies_Equation2 (G : Type*) [Magma G] (h : Equation30027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30029_implies_Equation2 (G : Type*) [Magma G] (h : Equation30029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30030_implies_Equation2 (G : Type*) [Magma G] (h : Equation30030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30031_implies_Equation2 (G : Type*) [Magma G] (h : Equation30031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30032_implies_Equation2 (G : Type*) [Magma G] (h : Equation30032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30034_implies_Equation2 (G : Type*) [Magma G] (h : Equation30034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30035_implies_Equation2 (G : Type*) [Magma G] (h : Equation30035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30036_implies_Equation2 (G : Type*) [Magma G] (h : Equation30036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30037_implies_Equation2 (G : Type*) [Magma G] (h : Equation30037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30038_implies_Equation2 (G : Type*) [Magma G] (h : Equation30038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30040_implies_Equation2 (G : Type*) [Magma G] (h : Equation30040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation30041_implies_Equation2 (G : Type*) [Magma G] (h : Equation30041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30042_implies_Equation2 (G : Type*) [Magma G] (h : Equation30042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation30043_implies_Equation2 (G : Type*) [Magma G] (h : Equation30043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30045_implies_Equation2 (G : Type*) [Magma G] (h : Equation30045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30046_implies_Equation2 (G : Type*) [Magma G] (h : Equation30046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30047_implies_Equation2 (G : Type*) [Magma G] (h : Equation30047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30048_implies_Equation2 (G : Type*) [Magma G] (h : Equation30048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30050_implies_Equation2 (G : Type*) [Magma G] (h : Equation30050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30051_implies_Equation2 (G : Type*) [Magma G] (h : Equation30051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30052_implies_Equation2 (G : Type*) [Magma G] (h : Equation30052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30053_implies_Equation2 (G : Type*) [Magma G] (h : Equation30053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30055_implies_Equation2 (G : Type*) [Magma G] (h : Equation30055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30056_implies_Equation2 (G : Type*) [Magma G] (h : Equation30056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30057_implies_Equation2 (G : Type*) [Magma G] (h : Equation30057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30058_implies_Equation2 (G : Type*) [Magma G] (h : Equation30058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30060_implies_Equation2 (G : Type*) [Magma G] (h : Equation30060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30061_implies_Equation2 (G : Type*) [Magma G] (h : Equation30061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30062_implies_Equation2 (G : Type*) [Magma G] (h : Equation30062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30063_implies_Equation2 (G : Type*) [Magma G] (h : Equation30063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30064_implies_Equation2 (G : Type*) [Magma G] (h : Equation30064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30066_implies_Equation2 (G : Type*) [Magma G] (h : Equation30066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq58 eq15


@[equational_result]
theorem Equation30067_implies_Equation2 (G : Type*) [Magma G] (h : Equation30067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation30068_implies_Equation2 (G : Type*) [Magma G] (h : Equation30068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30069_implies_Equation2 (G : Type*) [Magma G] (h : Equation30069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30071_implies_Equation2 (G : Type*) [Magma G] (h : Equation30071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30072_implies_Equation2 (G : Type*) [Magma G] (h : Equation30072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30073_implies_Equation2 (G : Type*) [Magma G] (h : Equation30073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30074_implies_Equation2 (G : Type*) [Magma G] (h : Equation30074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30076_implies_Equation2 (G : Type*) [Magma G] (h : Equation30076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30077_implies_Equation2 (G : Type*) [Magma G] (h : Equation30077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30078_implies_Equation2 (G : Type*) [Magma G] (h : Equation30078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30079_implies_Equation2 (G : Type*) [Magma G] (h : Equation30079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30081_implies_Equation2 (G : Type*) [Magma G] (h : Equation30081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30082_implies_Equation2 (G : Type*) [Magma G] (h : Equation30082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30083_implies_Equation2 (G : Type*) [Magma G] (h : Equation30083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30084_implies_Equation2 (G : Type*) [Magma G] (h : Equation30084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30086_implies_Equation2 (G : Type*) [Magma G] (h : Equation30086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30087_implies_Equation2 (G : Type*) [Magma G] (h : Equation30087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30088_implies_Equation2 (G : Type*) [Magma G] (h : Equation30088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30089_implies_Equation2 (G : Type*) [Magma G] (h : Equation30089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30090_implies_Equation2 (G : Type*) [Magma G] (h : Equation30090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30092_implies_Equation2 (G : Type*) [Magma G] (h : Equation30092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation30093_implies_Equation2 (G : Type*) [Magma G] (h : Equation30093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30094_implies_Equation2 (G : Type*) [Magma G] (h : Equation30094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30095_implies_Equation2 (G : Type*) [Magma G] (h : Equation30095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30096_implies_Equation2 (G : Type*) [Magma G] (h : Equation30096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30098_implies_Equation2 (G : Type*) [Magma G] (h : Equation30098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30099_implies_Equation2 (G : Type*) [Magma G] (h : Equation30099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30100_implies_Equation2 (G : Type*) [Magma G] (h : Equation30100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30101_implies_Equation2 (G : Type*) [Magma G] (h : Equation30101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30102_implies_Equation2 (G : Type*) [Magma G] (h : Equation30102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30104_implies_Equation2 (G : Type*) [Magma G] (h : Equation30104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30105_implies_Equation2 (G : Type*) [Magma G] (h : Equation30105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30106_implies_Equation2 (G : Type*) [Magma G] (h : Equation30106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30107_implies_Equation2 (G : Type*) [Magma G] (h : Equation30107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30108_implies_Equation2 (G : Type*) [Magma G] (h : Equation30108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30110_implies_Equation2 (G : Type*) [Magma G] (h : Equation30110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30111_implies_Equation2 (G : Type*) [Magma G] (h : Equation30111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30112_implies_Equation2 (G : Type*) [Magma G] (h : Equation30112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30113_implies_Equation2 (G : Type*) [Magma G] (h : Equation30113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30114_implies_Equation2 (G : Type*) [Magma G] (h : Equation30114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30116_implies_Equation2 (G : Type*) [Magma G] (h : Equation30116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30117_implies_Equation2 (G : Type*) [Magma G] (h : Equation30117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30118_implies_Equation2 (G : Type*) [Magma G] (h : Equation30118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30119_implies_Equation2 (G : Type*) [Magma G] (h : Equation30119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30120_implies_Equation2 (G : Type*) [Magma G] (h : Equation30120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30122_implies_Equation2 (G : Type*) [Magma G] (h : Equation30122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30123_implies_Equation2 (G : Type*) [Magma G] (h : Equation30123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30124_implies_Equation2 (G : Type*) [Magma G] (h : Equation30124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30125_implies_Equation2 (G : Type*) [Magma G] (h : Equation30125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30126_implies_Equation2 (G : Type*) [Magma G] (h : Equation30126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30127_implies_Equation2 (G : Type*) [Magma G] (h : Equation30127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30333_implies_Equation2 (G : Type*) [Magma G] (h : Equation30333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation30336_implies_Equation2 (G : Type*) [Magma G] (h : Equation30336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation30338_implies_Equation2 (G : Type*) [Magma G] (h : Equation30338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3)))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq10 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq10 eq15
  have eq20 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq18 eq9
  have eq21 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3)))) = X1 := superpose eq18 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq18 eq21
  have eq33 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq26 eq20
  have eq42 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq33 eq18
  have eq46 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq26 eq42
  have eq51 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq46 eq17
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq51 eq51
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq67 eq59


@[equational_result]
theorem Equation30339_implies_Equation2 (G : Type*) [Magma G] (h : Equation30339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq44 eq11


@[equational_result]
theorem Equation30340_implies_Equation2 (G : Type*) [Magma G] (h : Equation30340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq69 eq14


@[equational_result]
theorem Equation30343_implies_Equation2 (G : Type*) [Magma G] (h : Equation30343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq52 eq14


@[equational_result]
theorem Equation30346_implies_Equation2 (G : Type*) [Magma G] (h : Equation30346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq52 eq14


@[equational_result]
theorem Equation30348_implies_Equation2 (G : Type*) [Magma G] (h : Equation30348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq7 eq10
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq45 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq28 eq7
  have eq65 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ X3)) = ((X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ X3)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq10 eq15
  have eq78 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = X1 := superpose eq7 eq45
  have eq79 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq10 eq45
  have eq80 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) = X0 := superpose eq9 eq45
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) ◇ X0) := superpose eq7 eq45
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = (((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) := superpose eq10 eq45
  have eq84 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3))) = ((((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq9 eq45
  have eq91 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq45 eq7
  have eq205 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) = ((X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) := superpose eq13 eq45
  have eq222 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))) = (((X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) ◇ X0) ◇ X0) := superpose eq13 eq45
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = ((X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) ◇ X0) := superpose eq7 eq91
  have eq236 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq10 eq91
  have eq237 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) = (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3))))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq9 eq91
  have eq242 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) = ((X0 ◇ ((X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))))) ◇ X0) := superpose eq13 eq91
  have eq267 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq78 eq234
  have eq270 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose eq267 eq82
  have eq271 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = X1 := superpose eq267 eq78
  have eq298 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq79 eq236
  have eq299 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq298
  have eq302 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose eq299 eq83
  have eq313 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) = ((X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) := superpose eq302 eq65
  have eq342 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) = (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq80 eq237
  have eq343 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq342
  have eq344 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)))) = ((X1 ◇ X0) ◇ X1) := superpose eq267 eq343
  have eq345 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3))) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq344 eq84
  have eq348 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq271 eq345
  have eq349 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X1) := superpose eq348 eq9
  have eq419 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3))) ◇ X0) = (X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) := superpose eq205 eq242
  have eq420 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) = ((X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X0) := superpose eq348 eq419
  have eq421 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = (X0 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))))) := superpose eq349 eq420
  have eq422 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))) = (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) ◇ X0) := superpose eq421 eq222
  have eq426 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq7 eq422
  have eq440 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = (X0 ◇ (X1 ◇ X0)) := superpose eq426 eq421
  have eq441 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq440 eq28
  have eq442 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq440 eq7
  have eq506 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := superpose eq441 eq45
  have eq615 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq442 eq442
  have eq639 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq615 eq270
  have eq706 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = (X1 ◇ X0) := superpose eq442 eq639
  have eq707 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq706 eq440
  have eq708 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq707 eq506
  have eq725 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq707 eq442
  have eq807 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq725 eq708
  have eq825 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq807 eq707
  have eq826 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) = X0 := superpose eq825 eq313
  have eq863 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := superpose eq825 eq826
  have eq864 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq825 eq863
  have eq865 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq825 eq864
  have eq866 (X0 X3 : G) : X0 = X3 := superpose eq865 eq865
  have eq868 (X0 : G) : sK0 ≠ X0 := superpose eq866 eq8
  subsumption eq868 eq866


@[equational_result]
theorem Equation30350_implies_Equation2 (G : Type*) [Magma G] (h : Equation30350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq53 eq14


@[equational_result]
theorem Equation30352_implies_Equation2 (G : Type*) [Magma G] (h : Equation30352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq108 eq38


@[equational_result]
theorem Equation30353_implies_Equation2 (G : Type*) [Magma G] (h : Equation30353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation30354_implies_Equation2 (G : Type*) [Magma G] (h : Equation30354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation30356_implies_Equation2 (G : Type*) [Magma G] (h : Equation30356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X2))) = ((X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X2))) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq12
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq70 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)))) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq14 eq25
  have eq72 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq15 eq25
  have eq73 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq25 eq25
  have eq75 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq25 eq14
  have eq76 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((X3 ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X1 ◇ X3))) ◇ X3) := superpose eq25 eq9
  have eq79 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq25 eq7
  have eq85 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq25 eq14
  have eq90 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq10 eq70
  have eq91 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq25 eq72
  have eq92 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq10 eq91
  have eq93 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq15 eq92
  have eq95 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq93 eq75
  have eq140 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq15 eq79
  have eq147 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = (((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1)))) ◇ X1) ◇ X0) := superpose eq7 eq79
  have eq170 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq10 eq140
  have eq176 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq170 eq85
  have eq181 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq170 eq10
  have eq196 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X3) ◇ (X0 ◇ X0)))) = X2 := superpose eq170 eq90
  have eq198 (X0 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq170 eq95
  have eq217 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq170 eq147
  have eq218 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = (X1 ◇ X0) := superpose eq181 eq217
  have eq220 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq218 eq7
  have eq258 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) := superpose eq220 eq73
  have eq259 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) = ((X3 ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X3))) ◇ X3) := superpose eq220 eq76
  have eq268 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq220 eq176
  have eq276 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) = X1 := superpose eq220 eq258
  have eq277 (X1 X3 : G) : ((X3 ◇ (X1 ◇ (X1 ◇ X3))) ◇ X3) = X1 := superpose eq276 eq259
  have eq278 (X1 X3 : G) : ((X3 ◇ (X1 ◇ X1)) ◇ X3) = X1 := superpose eq170 eq277
  have eq279 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq278 eq198
  have eq285 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq279 eq170
  have eq293 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X0))) = X2 := superpose eq279 eq196
  have eq311 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (((X2 ◇ X0) ◇ X3) ◇ X0))) = X2 := superpose eq285 eq293
  have eq318 (X0 X1 X3 : G) : (X1 ◇ X0) = (((X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq279 eq268
  have eq319 (X0 X1 X3 : G) : (X1 ◇ X0) = (((X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq220 eq318
  have eq320 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq220 eq319
  have eq325 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) = X2 := superpose eq320 eq311
  have eq339 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq320 eq325
  have eq340 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq320 eq339
  have eq447 (X0 X2 : G) : X0 = X2 := superpose eq340 eq340
  have eq455 (X0 : G) : sK0 ≠ X0 := superpose eq447 eq8
  subsumption eq455 eq447


@[equational_result]
theorem Equation30358_implies_Equation2 (G : Type*) [Magma G] (h : Equation30358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation30361_implies_Equation2 (G : Type*) [Magma G] (h : Equation30361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation30362_implies_Equation2 (G : Type*) [Magma G] (h : Equation30362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation30364_implies_Equation2 (G : Type*) [Magma G] (h : Equation30364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X4) ◇ X5)))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq10 eq10
  have eq36 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq11 eq7
  have eq51 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq36 eq13
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq51 eq15
  have eq54 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq51 eq10
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq54 eq52
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq70 eq65


@[equational_result]
theorem Equation30365_implies_Equation2 (G : Type*) [Magma G] (h : Equation30365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation30366_implies_Equation2 (G : Type*) [Magma G] (h : Equation30366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30367_implies_Equation2 (G : Type*) [Magma G] (h : Equation30367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation30370_implies_Equation2 (G : Type*) [Magma G] (h : Equation30370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30373_implies_Equation2 (G : Type*) [Magma G] (h : Equation30373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30375_implies_Equation2 (G : Type*) [Magma G] (h : Equation30375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = ((X1 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X1) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq46 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = X1 := superpose eq15 eq7
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))))) ◇ X1) := superpose eq15 eq7
  have eq91 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) = (((((X1 ◇ X2) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ (X1 ◇ ((((X1 ◇ X2) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X1) ◇ X4))) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ (X1 ◇ ((((X1 ◇ X2) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X1) ◇ X4)))) := superpose eq13 eq9
  have eq102 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq46
  have eq140 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X3))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X3)))) := superpose eq15 eq11
  have eq142 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)))) := superpose eq11 eq11
  have eq156 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X0))) := superpose eq9 eq11
  have eq175 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq11 eq13
  have eq184 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq15 eq102
  have eq185 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq102 eq102
  have eq186 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X3) = X0 := superpose eq9 eq102
  have eq195 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X3))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)))) := superpose eq102 eq9
  have eq198 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((((X0 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)))) := superpose eq102 eq11
  have eq203 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq102 eq11
  have eq206 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq102 eq10
  have eq217 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) := superpose eq102 eq15
  have eq239 (X0 X1 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X3))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq102 eq195
  have eq240 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq185 eq239
  have eq242 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq102 eq198
  have eq243 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq185 eq242
  have eq244 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq240 eq243
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) := superpose eq244 eq217
  have eq252 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq251 eq184
  have eq253 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq252 eq102
  have eq256 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq252 eq203
  have eq258 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq252 eq206
  have eq265 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq253 eq140
  have eq271 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq253 eq256
  have eq273 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq244 eq258
  have eq274 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq273 eq271
  have eq276 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq273 eq274
  have eq282 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq276 eq265
  have eq288 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ (X1 ◇ X1)) := superpose eq276 eq282
  have eq289 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ X1) := superpose eq276 eq288
  have eq295 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = ((X0 ◇ X0) ◇ X0) := superpose eq289 eq15
  have eq348 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = (X0 ◇ X0) := superpose eq252 eq295
  have eq352 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq348 eq59
  have eq361 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq276 eq352
  have eq362 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq276 eq361
  have eq367 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = ((((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X1) ◇ X4))) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)))) := superpose eq362 eq91
  have eq368 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) = (((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq362 eq175
  have eq406 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = ((((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq362 eq367
  have eq407 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = ((((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1))) := superpose eq252 eq406
  have eq408 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (((X1 ◇ X1) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq276 eq407
  have eq409 (X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq276 eq408
  have eq410 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq244 eq368
  have eq411 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq409 eq410
  have eq412 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X0))) := superpose eq411 eq156
  have eq413 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) = (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X0))) := superpose eq276 eq412
  have eq414 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := superpose eq186 eq413
  have eq418 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)))) = X0 := superpose eq414 eq142
  have eq427 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := superpose eq414 eq418
  have eq428 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq289 eq427
  have eq429 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq428 eq362
  have eq447 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq429 eq7
  have eq507 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq429 eq447
  have eq695 (X0 X2 : G) : X0 = X2 := superpose eq507 eq507
  have eq697 (X0 : G) : sK0 ≠ X0 := superpose eq695 eq8
  subsumption eq697 eq695


@[equational_result]
theorem Equation30377_implies_Equation2 (G : Type*) [Magma G] (h : Equation30377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30380_implies_Equation2 (G : Type*) [Magma G] (h : Equation30380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation30383_implies_Equation2 (G : Type*) [Magma G] (h : Equation30383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation30385_implies_Equation2 (G : Type*) [Magma G] (h : Equation30385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq7
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq9 eq7
  have eq23 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq16
  have eq24 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq9 eq16
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq16 eq7
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq24 eq16
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq24 eq7
  have eq39 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq35 eq36
  have eq53 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq16 eq14
  have eq62 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq53 eq23
  have eq75 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq9 eq28
  have eq78 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq28 eq28
  have eq84 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq28 eq9
  have eq99 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) ◇ X1) := superpose eq16 eq75
  have eq102 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq16 eq78
  have eq111 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq102 eq39
  have eq114 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) ◇ X1) := superpose eq102 eq99
  have eq124 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq102 eq28
  have eq149 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq102 eq111
  have eq150 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq102 eq149
  have eq154 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) := superpose eq102 eq114
  have eq177 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq154 eq84
  have eq178 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq150 eq177
  have eq179 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq102 eq178
  have eq180 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq179 eq62
  have eq183 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq179 eq124
  have eq192 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq179 eq180
  have eq215 (X0 X1 : G) : X0 = X1 := superpose eq183 eq192
  have eq226 (X0 : G) : sK0 ≠ X0 := superpose eq215 eq8
  subsumption eq226 eq215


@[equational_result]
theorem Equation30386_implies_Equation2 (G : Type*) [Magma G] (h : Equation30386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)))) = ((X1 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq9 eq7
  have eq23 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X2 := superpose eq15 eq15
  have eq27 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq15 eq9
  have eq44 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X2 := superpose eq23 eq23
  have eq58 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq44 eq27
  have eq61 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq58 eq7
  have eq92 (X0 X2 : G) : X0 = X2 := superpose eq15 eq61
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq105 eq92


@[equational_result]
theorem Equation30387_implies_Equation2 (G : Type*) [Magma G] (h : Equation30387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation30389_implies_Equation2 (G : Type*) [Magma G] (h : Equation30389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq12
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)))) = X1 := superpose eq7 eq9
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq15 eq7
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = ((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq14 eq10
  have eq59 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq14 eq15
  have eq67 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq19
  have eq69 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq14 eq19
  have eq75 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq19 eq10
  have eq81 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq75 eq40
  have eq87 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0)) := superpose eq81 eq69
  have eq88 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq81 eq59
  have eq94 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq88 eq58
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq81 eq94
  have eq97 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq96 eq67
  have eq98 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq96 eq14
  have eq104 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq96 eq87
  have eq110 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq97 eq104
  have eq111 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq75 eq110
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq111 eq98
  have eq205 (X0 X2 : G) : X0 = X2 := superpose eq115 eq115
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq205 eq8
  subsumption eq207 eq205


@[equational_result]
theorem Equation30390_implies_Equation2 (G : Type*) [Magma G] (h : Equation30390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq10
  have eq30 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq30
  have eq41 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose eq30 eq10
  have eq98 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) ◇ X2))) = X0 := superpose eq37 eq10
  have eq106 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq98
  have eq136 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) = X3 := superpose eq30 eq15
  have eq164 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose eq106 eq37
  have eq167 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq106 eq7
  have eq175 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X2 := superpose eq106 eq15
  have eq176 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq106 eq30
  have eq211 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq176 eq41
  have eq214 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) = X1 := superpose eq211 eq164
  have eq215 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq214 eq167
  have eq218 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq215 eq211
  have eq227 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq218 eq175
  have eq229 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq37 eq227
  have eq230 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ (X0 ◇ (X2 ◇ X0))) = X3 := superpose eq229 eq136
  have eq360 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ (X3 ◇ X0)) ◇ X0) = X3 := superpose eq229 eq230
  have eq361 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ X0) = X3 := superpose eq229 eq360
  have eq362 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq229 eq361
  have eq363 (X0 X1 : G) : X0 = X1 := superpose eq218 eq362
  have eq368 (X0 : G) : sK0 ≠ X0 := superpose eq363 eq8
  subsumption eq368 eq363


@[equational_result]
theorem Equation30391_implies_Equation2 (G : Type*) [Magma G] (h : Equation30391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30393_implies_Equation2 (G : Type*) [Magma G] (h : Equation30393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = ((X1 ◇ (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ X4))) ◇ X1) := superpose eq10 eq11
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X1 := superpose eq11 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X4 ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq13 eq13
  have eq46 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X4)) = X0 := superpose eq7 eq13
  have eq47 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq13
  have eq87 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1) := superpose eq46 eq29
  have eq97 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq47 eq45
  have eq99 (X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1) = X2 := superpose eq97 eq87
  have eq100 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq97 eq99
  have eq101 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq100 eq32
  have eq114 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq100 eq101
  have eq115 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq100 eq114
  have eq116 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq100 eq115
  have eq118 (X0 X1 : G) : X0 = X1 := superpose eq100 eq116
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq123 eq118


@[equational_result]
theorem Equation30395_implies_Equation2 (G : Type*) [Magma G] (h : Equation30395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30397_implies_Equation2 (G : Type*) [Magma G] (h : Equation30397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X0) = (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X4) ◇ X4))))) := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X1 ◇ ((X0 ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3))) ◇ X0)) ◇ X1) := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X4) ◇ X4))))) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X2)))) ◇ (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X4) ◇ X4)))))) = X5 := superpose eq10 eq9
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))))) := superpose eq9 eq10
  have eq37 (X0 X2 X3 X5 : G) : ((((X0 ◇ X3) ◇ X0) ◇ (X5 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X2)))) ◇ ((X0 ◇ X3) ◇ X0)) = X5 := superpose eq13 eq28
  have eq39 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) ◇ X3)) = X1 := superpose eq7 eq17
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) := superpose eq17 eq17
  have eq43 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ ((X1 ◇ X3) ◇ X3)) := superpose eq7 eq17
  have eq57 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3))) ◇ (X4 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)))) = X4 := superpose eq17 eq9
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2)))) := superpose eq17 eq10
  have eq64 (X0 X1 X4 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) = X4 := superpose eq10 eq57
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq17 eq37
  have eq116 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3))) ◇ X0) = (((X0 ◇ X2) ◇ X2) ◇ ((X1 ◇ X4) ◇ X4)) := superpose eq10 eq43
  have eq323 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = X0 := superpose eq79 eq7
  have eq345 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)))) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq79 eq16
  have eq346 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)))) := superpose eq79 eq10
  have eq387 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq345
  have eq388 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq10 eq346
  have eq452 (X0 X1 X2 : G) : ((X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X2))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))))) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq9 eq13
  have eq501 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))))) ◇ X1) := superpose eq10 eq452
  have eq502 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq60 eq501
  have eq504 (X0 X1 X4 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X4 ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X4 := superpose eq502 eq64
  have eq505 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq502 eq387
  have eq506 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq17 eq505
  have eq533 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq323 eq323
  have eq540 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X0 := superpose eq43 eq323
  have eq546 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq323 eq79
  have eq584 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq540 eq388
  have eq586 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq584 eq506
  have eq589 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq584 eq533
  have eq590 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq586 eq60
  have eq600 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) := superpose eq589 eq35
  have eq605 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq589 eq502
  have eq607 (X0 X1 X4 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) = X4 := superpose eq589 eq504
  have eq608 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq589 eq590
  have eq614 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq17 eq546
  have eq615 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq584 eq614
  have eq618 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq615 eq600
  have eq624 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := superpose eq615 eq605
  have eq626 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ (X4 ◇ X0)) ◇ (X1 ◇ X0)) = X4 := superpose eq615 eq607
  have eq627 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = ((X0 ◇ X1) ◇ X0) := superpose eq615 eq608
  have eq636 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq615 eq618
  have eq637 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq615 eq636
  have eq638 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq615 eq637
  have eq703 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3)) := superpose eq638 eq42
  have eq943 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq638 eq624
  have eq945 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = (X0 ◇ (X1 ◇ X0)) := superpose eq638 eq627
  have eq958 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq945 eq7
  have eq963 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3)) = X1 := superpose eq945 eq39
  have eq1030 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X1 := superpose eq963 eq703
  have eq1036 (X0 X1 X3 X4 : G) : (X0 ◇ ((X1 ◇ X4) ◇ X4)) = ((X0 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X3))) ◇ X0) := superpose eq1030 eq116
  have eq1194 (X0 X1 X4 : G) : (X0 ◇ ((X1 ◇ X4) ◇ X4)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq1030 eq1036
  have eq1195 (X0 X1 X4 : G) : (X0 ◇ ((X1 ◇ X4) ◇ X4)) = X1 := superpose eq958 eq1194
  have eq1196 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1030 eq1195
  have eq1197 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq1196 eq943
  have eq1200 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ (X1 ◇ X0)) = X4 := superpose eq1196 eq626
  have eq1214 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X4 := superpose eq1196 eq1200
  have eq1215 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq1196 eq1214
  have eq1253 (X0 X1 : G) : X0 = X1 := superpose eq1197 eq1215
  have eq1272 (X0 : G) : sK0 ≠ X0 := superpose eq1253 eq8
  subsumption eq1272 eq1253


@[equational_result]
theorem Equation30398_implies_Equation2 (G : Type*) [Magma G] (h : Equation30398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X3)) ◇ ((X1 ◇ X3) ◇ X3)))) = ((X1 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ ((X2 ◇ ((X1 ◇ X4) ◇ X4)) ◇ ((X1 ◇ X4) ◇ X4)))) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X4)))) = ((X1 ◇ X0) ◇ X4) := superpose eq9 eq7
  have eq23 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X4) = (((X1 ◇ X3) ◇ X4) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X4)))) := superpose eq10 eq20
  have eq36 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2)))) ◇ ((X0 ◇ X2) ◇ X2)) = X4 := superpose eq10 eq9
  have eq48 (X0 X2 X4 : G) : (((X0 ◇ X4) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X4 := superpose eq23 eq36
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) ◇ X3)) = X2 := superpose eq7 eq48
  have eq142 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq50
  have eq299 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq142
  have eq955 (X0 X2 : G) : X0 = X2 := superpose eq142 eq299
  have eq974 (X0 : G) : sK0 ≠ X0 := superpose eq955 eq8
  subsumption eq974 eq955


@[equational_result]
theorem Equation30399_implies_Equation2 (G : Type*) [Magma G] (h : Equation30399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30401_implies_Equation2 (G : Type*) [Magma G] (h : Equation30401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq33 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X6)) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X0)) := superpose eq11 eq11
  have eq36 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) = X1 := superpose eq11 eq7
  have eq41 (X0 X1 X2 X3 X5 X6 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X6)) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq10 eq33
  have eq49 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq13
  have eq89 (X0 X1 X5 X6 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X6)) ◇ X1) = X1 := superpose eq49 eq41
  have eq101 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq49 eq89
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X1 := superpose eq101 eq36
  have eq110 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq101 eq102
  have eq111 (X0 X3 : G) : X0 = X3 := superpose eq110 eq110
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq116 eq111


@[equational_result]
theorem Equation30402_implies_Equation2 (G : Type*) [Magma G] (h : Equation30402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X4 ◇ (X0 ◇ X5))) ◇ X2) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X4))) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq10 eq7
  have eq26 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X4 := superpose eq23 eq9
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq10 eq26
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq44 eq37


@[equational_result]
theorem Equation30403_implies_Equation2 (G : Type*) [Magma G] (h : Equation30403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X4 ◇ (X0 ◇ X5))) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X4) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30404_implies_Equation2 (G : Type*) [Magma G] (h : Equation30404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X4 ◇ (X0 ◇ X6))) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30406_implies_Equation2 (G : Type*) [Magma G] (h : Equation30406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq12 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq12 eq19
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq20 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq9 eq22
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq37 eq27


@[equational_result]
theorem Equation30407_implies_Equation2 (G : Type*) [Magma G] (h : Equation30407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation30408_implies_Equation2 (G : Type*) [Magma G] (h : Equation30408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30410_implies_Equation2 (G : Type*) [Magma G] (h : Equation30410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq11 eq10
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq11 eq17
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq18 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq9 eq19
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq33 eq23


@[equational_result]
theorem Equation30412_implies_Equation2 (G : Type*) [Magma G] (h : Equation30412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30415_implies_Equation2 (G : Type*) [Magma G] (h : Equation30415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30416_implies_Equation2 (G : Type*) [Magma G] (h : Equation30416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq66 eq13


@[equational_result]
theorem Equation30418_implies_Equation2 (G : Type*) [Magma G] (h : Equation30418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = ((X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq12 eq10
  have eq22 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq12 eq21
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq22 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq9 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation30419_implies_Equation2 (G : Type*) [Magma G] (h : Equation30419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation30420_implies_Equation2 (G : Type*) [Magma G] (h : Equation30420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation30421_implies_Equation2 (G : Type*) [Magma G] (h : Equation30421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30423_implies_Equation2 (G : Type*) [Magma G] (h : Equation30423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0)))) = X1 := superpose eq9 eq9
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq14 eq11
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq7 eq62
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq156 eq72


@[equational_result]
theorem Equation30425_implies_Equation2 (G : Type*) [Magma G] (h : Equation30425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30427_implies_Equation2 (G : Type*) [Magma G] (h : Equation30427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ X1) ◇ (X0 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)))) := superpose eq7 eq9
  have eq42 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))))) = X1 := superpose eq7 eq11
  have eq56 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = X1 := superpose eq13 eq42
  have eq94 (X0 X3 : G) : X0 = X3 := superpose eq56 eq56
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq175 eq94


@[equational_result]
theorem Equation30428_implies_Equation2 (G : Type*) [Magma G] (h : Equation30428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((((X3 ◇ X1) ◇ X1) ◇ X2) ◇ X2))) = ((X1 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X4 ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3))) ◇ ((X1 ◇ X4) ◇ X4)))) = X2 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq10 eq9
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X1 := superpose eq10 eq7
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ ((X3 ◇ X4) ◇ X4)))) = X1 := superpose eq10 eq9
  have eq42 (X0 X1 X2 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq29 eq29
  have eq182 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1)) = X0 := superpose eq30 eq28
  have eq247 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) = X0 := superpose eq182 eq182
  have eq264 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) = ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq182 eq29
  have eq265 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2)) ◇ (((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) ◇ X1))) = X0 := superpose eq182 eq42
  have eq270 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) = X0 := superpose eq182 eq247
  have eq271 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1))) = X0 := superpose eq182 eq270
  have eq280 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) ◇ X1)) ◇ (((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) ◇ X1))) = X0 := superpose eq182 eq265
  have eq321 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) ◇ X3) ◇ ((X4 ◇ (X2 ◇ ((X0 ◇ X4) ◇ X4))) ◇ (X0 ◇ ((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) ◇ X3))))) = X1 := superpose eq182 eq11
  have eq352 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) ◇ X3) ◇ ((X4 ◇ (X2 ◇ ((X0 ◇ X4) ◇ X4))) ◇ X0))) = X1 := superpose eq182 eq321
  have eq353 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) ◇ X3) ◇ X2)) = X1 := superpose eq7 eq352
  have eq354 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2)) = X0 := superpose eq353 eq280
  have eq355 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq354 eq271
  have eq374 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq355 eq29
  have eq409 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) = X0 := superpose eq374 eq264
  have eq422 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq409 eq354
  have eq430 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq422 eq7
  have eq602 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq422 eq430
  have eq603 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq422 eq602
  have eq604 (X0 X1 : G) : X0 = X1 := superpose eq355 eq603
  have eq609 (X0 : G) : sK0 ≠ X0 := superpose eq604 eq8
  subsumption eq609 eq604


@[equational_result]
theorem Equation30429_implies_Equation2 (G : Type*) [Magma G] (h : Equation30429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30431_implies_Equation2 (G : Type*) [Magma G] (h : Equation30431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X3)))))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X4)))))) := superpose eq9 eq7
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X1)))) := superpose eq11 eq22
  have eq34 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ (X4 ◇ X1)) ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq10
  have eq54 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq34 eq34
  have eq97 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ ((X0 ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X3)) ◇ X0)) ◇ X3) := superpose eq11 eq7
  have eq98 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq11 eq9
  have eq117 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq26 eq98
  have eq125 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3)) := superpose eq34 eq117
  have eq131 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq34 eq117
  have eq140 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq10 eq117
  have eq144 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq117 eq10
  have eq159 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) := superpose eq117 eq34
  have eq165 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X3) := superpose eq131 eq97
  have eq171 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X3 ◇ (X2 ◇ X0)) ◇ X3) := superpose eq131 eq165
  have eq175 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq54 eq144
  have eq185 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3)) := superpose eq175 eq125
  have eq212 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) = X0 := superpose eq34 eq171
  have eq222 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3)))) := superpose eq7 eq171
  have eq279 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq212 eq185
  have eq282 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq131 eq222
  have eq283 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq282 eq175
  have eq295 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq283 eq279
  have eq313 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq295 eq159
  have eq322 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq313 eq140
  have eq324 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq322 eq295
  have eq331 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq324 eq7
  have eq377 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq324 eq331
  have eq378 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq324 eq377
  have eq379 (X0 X3 : G) : X0 = X3 := superpose eq378 eq378
  have eq381 (X0 : G) : sK0 ≠ X0 := superpose eq379 eq8
  subsumption eq381 eq379


@[equational_result]
theorem Equation30433_implies_Equation2 (G : Type*) [Magma G] (h : Equation30433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30435_implies_Equation2 (G : Type*) [Magma G] (h : Equation30435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X1) ◇ X3) ◇ (X0 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X2) := superpose eq11 eq7
  have eq97 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X2 ◇ X1) ◇ X2) := superpose eq12 eq85
  have eq105 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X4) = X0 := superpose eq7 eq97
  have eq235 (X0 X3 : G) : X0 = X3 := superpose eq105 eq105
  have eq440 (X0 : G) : sK0 ≠ X0 := superpose eq235 eq8
  subsumption eq440 eq235


@[equational_result]
theorem Equation30436_implies_Equation2 (G : Type*) [Magma G] (h : Equation30436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X5))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X4)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = X3 := superpose eq7 eq10
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq9 eq20
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq146 eq60


@[equational_result]
theorem Equation30437_implies_Equation2 (G : Type*) [Magma G] (h : Equation30437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X5) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X0)) ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq9
  have eq21 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = X4 := superpose eq12 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation30438_implies_Equation2 (G : Type*) [Magma G] (h : Equation30438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30441_implies_Equation2 (G : Type*) [Magma G] (h : Equation30441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq45 eq11


@[equational_result]
theorem Equation30442_implies_Equation2 (G : Type*) [Magma G] (h : Equation30442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30444_implies_Equation2 (G : Type*) [Magma G] (h : Equation30444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X2 ◇ X2) ◇ X1)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X1 := superpose eq9 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ X3) ◇ ((X2 ◇ X2) ◇ X0))) = ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq9 eq16
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq16 eq16
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq16 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ X3) ◇ ((X2 ◇ X2) ◇ X0))) = (X1 ◇ ((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq16 eq19
  have eq38 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq23 eq23
  have eq39 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq23
  have eq79 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq23 eq38
  have eq105 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq39 eq79
  have eq110 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := superpose eq105 eq9
  have eq111 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X1 := superpose eq105 eq16
  have eq127 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ X0))) = (X1 ◇ (X3 ◇ X3)) := superpose eq111 eq29
  have eq134 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := superpose eq111 eq110
  have eq144 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X1 := superpose eq111 eq127
  have eq146 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq144 eq38
  have eq150 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq146 eq28
  have eq165 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X1) ◇ X0) = X0 := superpose eq146 eq134
  have eq166 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq146 eq165
  have eq167 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq146 eq166
  have eq172 (X0 X1 : G) : X0 = X1 := superpose eq167 eq150
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq172 eq8
  subsumption eq191 eq172


@[equational_result]
theorem Equation30446_implies_Equation2 (G : Type*) [Magma G] (h : Equation30446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation30448_implies_Equation2 (G : Type*) [Magma G] (h : Equation30448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq9 eq9
  have eq67 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq9 eq13
  have eq116 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq67 eq7
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq9 eq116
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq162 eq143


@[equational_result]
theorem Equation30449_implies_Equation2 (G : Type*) [Magma G] (h : Equation30449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq66 eq11


@[equational_result]
theorem Equation30450_implies_Equation2 (G : Type*) [Magma G] (h : Equation30450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30452_implies_Equation2 (G : Type*) [Magma G] (h : Equation30452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq9 eq9
  have eq70 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq9 eq13
  have eq119 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq70 eq7
  have eq145 (X0 X3 : G) : X0 = X3 := superpose eq9 eq119
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq164 eq145


@[equational_result]
theorem Equation30453_implies_Equation2 (G : Type*) [Magma G] (h : Equation30453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30454_implies_Equation2 (G : Type*) [Magma G] (h : Equation30454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation30455_implies_Equation2 (G : Type*) [Magma G] (h : Equation30455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30457_implies_Equation2 (G : Type*) [Magma G] (h : Equation30457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq37 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq13
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq37 eq7
  have eq86 (X0 X3 : G) : X0 = X3 := superpose eq9 eq72
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq113 eq86


@[equational_result]
theorem Equation30458_implies_Equation2 (G : Type*) [Magma G] (h : Equation30458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation30459_implies_Equation2 (G : Type*) [Magma G] (h : Equation30459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation30460_implies_Equation2 (G : Type*) [Magma G] (h : Equation30460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30462_implies_Equation2 (G : Type*) [Magma G] (h : Equation30462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq37 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq13
  have eq77 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq37 eq7
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq9 eq77
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq112 eq85


@[equational_result]
theorem Equation30463_implies_Equation2 (G : Type*) [Magma G] (h : Equation30463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq10
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq132 eq45


@[equational_result]
theorem Equation30464_implies_Equation2 (G : Type*) [Magma G] (h : Equation30464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq9 eq9
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq147 eq61


@[equational_result]
theorem Equation30465_implies_Equation2 (G : Type*) [Magma G] (h : Equation30465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30467_implies_Equation2 (G : Type*) [Magma G] (h : Equation30467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq52 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq14
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq52 eq7
  have eq113 (X0 X3 : G) : X0 = X3 := superpose eq10 eq96
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq113 eq8
  subsumption eq132 eq113


@[equational_result]
theorem Equation30468_implies_Equation2 (G : Type*) [Magma G] (h : Equation30468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30469_implies_Equation2 (G : Type*) [Magma G] (h : Equation30469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30470_implies_Equation2 (G : Type*) [Magma G] (h : Equation30470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30472_implies_Equation2 (G : Type*) [Magma G] (h : Equation30472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5)))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq53 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq10 eq14
  have eq82 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X2 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5)))) = X1 := superpose eq53 eq12
  have eq89 (X0 X1 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X1 := superpose eq53 eq82
  have eq96 (X0 X5 : G) : X0 = X5 := superpose eq9 eq89
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq124 eq96


@[equational_result]
theorem Equation30473_implies_Equation2 (G : Type*) [Magma G] (h : Equation30473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation30474_implies_Equation2 (G : Type*) [Magma G] (h : Equation30474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation30475_implies_Equation2 (G : Type*) [Magma G] (h : Equation30475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30477_implies_Equation2 (G : Type*) [Magma G] (h : Equation30477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X7 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X7))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq43 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq14
  have eq80 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq43 eq7
  have eq95 (X0 X4 : G) : X0 = X4 := superpose eq9 eq80
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq123 eq95


@[equational_result]
theorem Equation30478_implies_Equation2 (G : Type*) [Magma G] (h : Equation30478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30479_implies_Equation2 (G : Type*) [Magma G] (h : Equation30479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30480_implies_Equation2 (G : Type*) [Magma G] (h : Equation30480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30481_implies_Equation2 (G : Type*) [Magma G] (h : Equation30481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X9 : G) : (X0 ◇ X9) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation30484_implies_Equation2 (G : Type*) [Magma G] (h : Equation30484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation30487_implies_Equation2 (G : Type*) [Magma G] (h : Equation30487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq70 eq13


@[equational_result]
theorem Equation30489_implies_Equation2 (G : Type*) [Magma G] (h : Equation30489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)))) = X0 := superpose eq7 eq9
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq10 eq9
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq10 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq15
  have eq26 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq22 eq7
  have eq36 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq26 eq19
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq36 eq22
  have eq40 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq38 eq26
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq54 eq52


@[equational_result]
theorem Equation30491_implies_Equation2 (G : Type*) [Magma G] (h : Equation30491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq73 eq13


@[equational_result]
theorem Equation30494_implies_Equation2 (G : Type*) [Magma G] (h : Equation30494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq50 eq14


@[equational_result]
theorem Equation30497_implies_Equation2 (G : Type*) [Magma G] (h : Equation30497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq74 eq14


@[equational_result]
theorem Equation30499_implies_Equation2 (G : Type*) [Magma G] (h : Equation30499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)))) ◇ X1) = X0 := superpose eq9 eq7
  have eq34 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0) = X1 := superpose eq25 eq24
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) := superpose eq10 eq10
  have eq67 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)) = X1 := superpose eq25 eq10
  have eq75 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq67 eq29
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq75 eq34
  have eq97 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) := superpose eq82 eq38
  have eq112 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0))) ◇ X0) := superpose eq82 eq97
  have eq113 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq82 eq112
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq82 eq113
  have eq116 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq114 eq75
  have eq150 (X0 X1 : G) : X0 = X1 := superpose eq114 eq116
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq150 eq8
  subsumption eq155 eq150


@[equational_result]
theorem Equation30501_implies_Equation2 (G : Type*) [Magma G] (h : Equation30501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation30503_implies_Equation2 (G : Type*) [Magma G] (h : Equation30503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation30505_implies_Equation2 (G : Type*) [Magma G] (h : Equation30505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation30507_implies_Equation2 (G : Type*) [Magma G] (h : Equation30507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation30509_implies_Equation2 (G : Type*) [Magma G] (h : Equation30509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation30513_implies_Equation2 (G : Type*) [Magma G] (h : Equation30513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation30515_implies_Equation2 (G : Type*) [Magma G] (h : Equation30515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation30516_implies_Equation2 (G : Type*) [Magma G] (h : Equation30516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq10 eq7
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq22
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5))) ◇ X3) = X2 := superpose eq25 eq11
  have eq38 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq25 eq26
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq38 eq38
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq41 eq39


@[equational_result]
theorem Equation30517_implies_Equation2 (G : Type*) [Magma G] (h : Equation30517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X4) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq78 eq17


@[equational_result]
theorem Equation30518_implies_Equation2 (G : Type*) [Magma G] (h : Equation30518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X7 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation30521_implies_Equation2 (G : Type*) [Magma G] (h : Equation30521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30524_implies_Equation2 (G : Type*) [Magma G] (h : Equation30524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30526_implies_Equation2 (G : Type*) [Magma G] (h : Equation30526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) := superpose eq10 eq10
  have eq17 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = X1 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3))) ◇ X0) := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3))) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq10 eq7
  have eq23 (X0 X1 X3 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X1 := superpose eq17 eq14
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq18
  have eq26 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq24 eq13
  have eq29 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq24 eq26
  have eq32 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq24 eq22
  have eq33 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq32 eq29
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq33 eq20
  have eq42 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq34 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq34 eq42
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq48 eq48
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq57 eq55


@[equational_result]
theorem Equation30527_implies_Equation2 (G : Type*) [Magma G] (h : Equation30527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3)))) ◇ X3) = X2 := superpose eq10 eq9
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))))) ◇ X3) = X2 := superpose eq10 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3))))) ◇ X3) = X2 := superpose eq10 eq12
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ X3)))) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq12 eq7
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3)))))) ◇ X3) = X2 := superpose eq10 eq38
  have eq60 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3))))))) ◇ X3) = X2 := superpose eq10 eq59
  have eq71 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ X3)))) = (X1 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq10 eq47
  have eq85 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq16 eq16
  have eq86 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) ◇ X3))) = X2 := superpose eq10 eq16
  have eq95 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq85 eq16
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := superpose eq85 eq7
  have eq100 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq85 eq10
  have eq108 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3))))))) ◇ X3) = X2 := superpose eq85 eq60
  have eq110 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X3)))) := superpose eq85 eq71
  have eq119 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := superpose eq85 eq95
  have eq120 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := superpose eq85 eq119
  have eq251 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3)))))))) ◇ X3) = X2 := superpose eq85 eq108
  have eq252 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3))))))))) ◇ X3) = X2 := superpose eq85 eq251
  have eq253 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3)))))))))) ◇ X3) = X2 := superpose eq85 eq252
  have eq254 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3))))))))))) ◇ X3) = X2 := superpose eq85 eq253
  have eq255 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)))))))))))) ◇ X3) = X2 := superpose eq85 eq254
  have eq256 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))))))))))) ◇ X3) = X2 := superpose eq85 eq255
  have eq257 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))))))))))) ◇ X3) = X2 := superpose eq85 eq256
  have eq275 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3))))) := superpose eq85 eq110
  have eq276 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3)))))) := superpose eq85 eq275
  have eq277 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))))) := superpose eq85 eq276
  have eq278 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))))) := superpose eq85 eq277
  have eq298 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) ◇ X3)))) = X2 := superpose eq85 eq86
  have eq299 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3))))) = X2 := superpose eq85 eq298
  have eq300 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3)))))) = X2 := superpose eq85 eq299
  have eq301 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3))))))) = X2 := superpose eq85 eq300
  have eq302 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)))))))) = X2 := superpose eq85 eq301
  have eq303 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X3))))))))) = X2 := superpose eq85 eq302
  have eq304 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))))))))) = X2 := superpose eq85 eq303
  have eq305 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))))))))) = X2 := superpose eq85 eq304
  have eq414 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) := superpose eq99 eq120
  have eq423 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq120 eq120
  have eq425 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))))) = X2 := superpose eq85 eq120
  have eq430 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X3))) := superpose eq120 eq100
  have eq435 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq120 eq414
  have eq448 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))))))))) ◇ X3) = X2 := superpose eq435 eq257
  have eq449 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq435 eq278
  have eq474 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))))) ◇ X3) = X2 := superpose eq435 eq448
  have eq502 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))))))) = X2 := superpose eq423 eq305
  have eq516 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))))))) = X2 := superpose eq85 eq425
  have eq517 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))))) = X2 := superpose eq85 eq516
  have eq518 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq423 eq517
  have eq525 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3)))) := superpose eq85 eq430
  have eq526 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3))))) := superpose eq85 eq525
  have eq527 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) := superpose eq435 eq526
  have eq528 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq85 eq527
  have eq529 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq85 eq528
  have eq530 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq85 eq529
  have eq535 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))) = X2 := superpose eq530 eq502
  have eq541 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) = X2 := superpose eq530 eq535
  have eq542 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq530 eq541
  have eq547 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) = X3 := superpose eq542 eq449
  have eq549 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) = X3 := superpose eq542 eq547
  have eq551 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq549 eq518
  have eq568 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) ◇ X3) = X2 := superpose eq551 eq474
  have eq578 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X3) = X2 := superpose eq551 eq568
  have eq579 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X3) = X2 := superpose eq551 eq578
  have eq580 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq551 eq579
  have eq589 (X0 X2 : G) : X0 = X2 := superpose eq580 eq580
  have eq591 (X0 : G) : sK0 ≠ X0 := superpose eq589 eq8
  subsumption eq591 eq589


@[equational_result]
theorem Equation30528_implies_Equation2 (G : Type*) [Magma G] (h : Equation30528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30531_implies_Equation2 (G : Type*) [Magma G] (h : Equation30531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation30533_implies_Equation2 (G : Type*) [Magma G] (h : Equation30533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30534_implies_Equation2 (G : Type*) [Magma G] (h : Equation30534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30536_implies_Equation2 (G : Type*) [Magma G] (h : Equation30536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30537_implies_Equation2 (G : Type*) [Magma G] (h : Equation30537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30538_implies_Equation2 (G : Type*) [Magma G] (h : Equation30538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30540_implies_Equation2 (G : Type*) [Magma G] (h : Equation30540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq34 eq13


@[equational_result]
theorem Equation30541_implies_Equation2 (G : Type*) [Magma G] (h : Equation30541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X0 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X1 ◇ X0)) := superpose eq10 eq10
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0) ◇ X2) := superpose eq10 eq9
  have eq45 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := superpose eq10 eq15
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))))) := superpose eq16 eq16
  have eq215 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq29
  have eq276 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := superpose eq10 eq215
  have eq311 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))))) := superpose eq276 eq61
  have eq314 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq276 eq311
  have eq315 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = X3 := superpose eq314 eq9
  have eq461 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq314 eq315
  have eq464 (X0 X3 : G) : X0 = X3 := superpose eq45 eq461
  have eq489 (X0 : G) : sK0 ≠ X0 := superpose eq464 eq8
  subsumption eq489 eq464


@[equational_result]
theorem Equation30542_implies_Equation2 (G : Type*) [Magma G] (h : Equation30542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X0 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30544_implies_Equation2 (G : Type*) [Magma G] (h : Equation30544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30545_implies_Equation2 (G : Type*) [Magma G] (h : Equation30545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30546_implies_Equation2 (G : Type*) [Magma G] (h : Equation30546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30548_implies_Equation2 (G : Type*) [Magma G] (h : Equation30548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30549_implies_Equation2 (G : Type*) [Magma G] (h : Equation30549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30550_implies_Equation2 (G : Type*) [Magma G] (h : Equation30550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30552_implies_Equation2 (G : Type*) [Magma G] (h : Equation30552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30553_implies_Equation2 (G : Type*) [Magma G] (h : Equation30553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30554_implies_Equation2 (G : Type*) [Magma G] (h : Equation30554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30555_implies_Equation2 (G : Type*) [Magma G] (h : Equation30555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30557_implies_Equation2 (G : Type*) [Magma G] (h : Equation30557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq94 eq34


@[equational_result]
theorem Equation30559_implies_Equation2 (G : Type*) [Magma G] (h : Equation30559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation30561_implies_Equation2 (G : Type*) [Magma G] (h : Equation30561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation30562_implies_Equation2 (G : Type*) [Magma G] (h : Equation30562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) = X1 := superpose eq10 eq7
  have eq21 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)))) ◇ X2) = X3 := superpose eq10 eq7
  have eq92 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq18 eq19
  have eq106 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq92 eq7
  have eq107 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) = X3 := superpose eq92 eq9
  have eq158 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq92 eq106
  have eq159 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X0) ◇ X2)) = X3 := superpose eq92 eq107
  have eq160 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X2)) = X3 := superpose eq92 eq159
  have eq161 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ X2)) = X3 := superpose eq92 eq160
  have eq162 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X3 := superpose eq161 eq21
  have eq165 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq158 eq162
  have eq166 (X0 X3 : G) : X0 = X3 := superpose eq165 eq165
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq177 eq166


@[equational_result]
theorem Equation30563_implies_Equation2 (G : Type*) [Magma G] (h : Equation30563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation30565_implies_Equation2 (G : Type*) [Magma G] (h : Equation30565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X3)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq18 (X0 X2 X4 : G) : ((X4 ◇ (X4 ◇ X2)) ◇ X4) = X0 := superpose eq7 eq10
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq159 eq74


@[equational_result]
theorem Equation30567_implies_Equation2 (G : Type*) [Magma G] (h : Equation30567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq69 eq14


@[equational_result]
theorem Equation30569_implies_Equation2 (G : Type*) [Magma G] (h : Equation30569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq74 eq19


@[equational_result]
theorem Equation30570_implies_Equation2 (G : Type*) [Magma G] (h : Equation30570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X5))) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) = X3 := superpose eq7 eq7
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ X3)) := superpose eq9 eq7
  have eq81 (X0 X2 X4 X5 : G) : (X2 ◇ (X4 ◇ X5)) = X0 := superpose eq7 eq74
  have eq209 (X0 X6 : G) : X0 = X6 := superpose eq9 eq81
  have eq381 (X0 : G) : sK0 ≠ X0 := superpose eq209 eq8
  subsumption eq381 eq209


@[equational_result]
theorem Equation30571_implies_Equation2 (G : Type*) [Magma G] (h : Equation30571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X5))) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation30572_implies_Equation2 (G : Type*) [Magma G] (h : Equation30572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 X7 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X0) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation30574_implies_Equation2 (G : Type*) [Magma G] (h : Equation30574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X1 := superpose eq7 eq7
  have eq23 (X0 X1 : G) : X0 = X1 := superpose eq9 eq10
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq29 eq23


@[equational_result]
theorem Equation30576_implies_Equation2 (G : Type*) [Magma G] (h : Equation30576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation30578_implies_Equation2 (G : Type*) [Magma G] (h : Equation30578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30579_implies_Equation2 (G : Type*) [Magma G] (h : Equation30579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30580_implies_Equation2 (G : Type*) [Magma G] (h : Equation30580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30582_implies_Equation2 (G : Type*) [Magma G] (h : Equation30582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30583_implies_Equation2 (G : Type*) [Magma G] (h : Equation30583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30584_implies_Equation2 (G : Type*) [Magma G] (h : Equation30584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30586_implies_Equation2 (G : Type*) [Magma G] (h : Equation30586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30587_implies_Equation2 (G : Type*) [Magma G] (h : Equation30587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30588_implies_Equation2 (G : Type*) [Magma G] (h : Equation30588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30589_implies_Equation2 (G : Type*) [Magma G] (h : Equation30589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30593_implies_Equation2 (G : Type*) [Magma G] (h : Equation30593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation30595_implies_Equation2 (G : Type*) [Magma G] (h : Equation30595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30596_implies_Equation2 (G : Type*) [Magma G] (h : Equation30596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30597_implies_Equation2 (G : Type*) [Magma G] (h : Equation30597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30599_implies_Equation2 (G : Type*) [Magma G] (h : Equation30599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30600_implies_Equation2 (G : Type*) [Magma G] (h : Equation30600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30601_implies_Equation2 (G : Type*) [Magma G] (h : Equation30601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30603_implies_Equation2 (G : Type*) [Magma G] (h : Equation30603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30604_implies_Equation2 (G : Type*) [Magma G] (h : Equation30604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30605_implies_Equation2 (G : Type*) [Magma G] (h : Equation30605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30606_implies_Equation2 (G : Type*) [Magma G] (h : Equation30606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30608_implies_Equation2 (G : Type*) [Magma G] (h : Equation30608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation30609_implies_Equation2 (G : Type*) [Magma G] (h : Equation30609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq65 eq17


@[equational_result]
theorem Equation30610_implies_Equation2 (G : Type*) [Magma G] (h : Equation30610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X5))) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X0))) ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq9 eq11
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation30611_implies_Equation2 (G : Type*) [Magma G] (h : Equation30611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X6 X7 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X0) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation30613_implies_Equation2 (G : Type*) [Magma G] (h : Equation30613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30614_implies_Equation2 (G : Type*) [Magma G] (h : Equation30614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30615_implies_Equation2 (G : Type*) [Magma G] (h : Equation30615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30616_implies_Equation2 (G : Type*) [Magma G] (h : Equation30616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30618_implies_Equation2 (G : Type*) [Magma G] (h : Equation30618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30619_implies_Equation2 (G : Type*) [Magma G] (h : Equation30619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30620_implies_Equation2 (G : Type*) [Magma G] (h : Equation30620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30621_implies_Equation2 (G : Type*) [Magma G] (h : Equation30621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30623_implies_Equation2 (G : Type*) [Magma G] (h : Equation30623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30624_implies_Equation2 (G : Type*) [Magma G] (h : Equation30624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30625_implies_Equation2 (G : Type*) [Magma G] (h : Equation30625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30626_implies_Equation2 (G : Type*) [Magma G] (h : Equation30626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30628_implies_Equation2 (G : Type*) [Magma G] (h : Equation30628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30629_implies_Equation2 (G : Type*) [Magma G] (h : Equation30629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30630_implies_Equation2 (G : Type*) [Magma G] (h : Equation30630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30631_implies_Equation2 (G : Type*) [Magma G] (h : Equation30631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30632_implies_Equation2 (G : Type*) [Magma G] (h : Equation30632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30634_implies_Equation2 (G : Type*) [Magma G] (h : Equation30634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation30635_implies_Equation2 (G : Type*) [Magma G] (h : Equation30635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation30636_implies_Equation2 (G : Type*) [Magma G] (h : Equation30636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30638_implies_Equation2 (G : Type*) [Magma G] (h : Equation30638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation30640_implies_Equation2 (G : Type*) [Magma G] (h : Equation30640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30643_implies_Equation2 (G : Type*) [Magma G] (h : Equation30643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq55 eq11


@[equational_result]
theorem Equation30644_implies_Equation2 (G : Type*) [Magma G] (h : Equation30644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30646_implies_Equation2 (G : Type*) [Magma G] (h : Equation30646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation30647_implies_Equation2 (G : Type*) [Magma G] (h : Equation30647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq64 eq12


@[equational_result]
theorem Equation30648_implies_Equation2 (G : Type*) [Magma G] (h : Equation30648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30649_implies_Equation2 (G : Type*) [Magma G] (h : Equation30649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30651_implies_Equation2 (G : Type*) [Magma G] (h : Equation30651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq52 eq15


@[equational_result]
theorem Equation30653_implies_Equation2 (G : Type*) [Magma G] (h : Equation30653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30655_implies_Equation2 (G : Type*) [Magma G] (h : Equation30655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation30657_implies_Equation2 (G : Type*) [Magma G] (h : Equation30657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30659_implies_Equation2 (G : Type*) [Magma G] (h : Equation30659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X2 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ (X4 ◇ ((X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X4))) ◇ X1) := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X5 ◇ ((X0 ◇ (X4 ◇ (X2 ◇ X4))) ◇ X5))) ◇ X0) = (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X2 ◇ X0)) = (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq7 eq9
  have eq17 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) = ((X0 ◇ (X4 ◇ (X2 ◇ X4))) ◇ X0) := superpose eq9 eq9
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (((X0 ◇ (X5 ◇ (X2 ◇ X5))) ◇ X3) ◇ X4))) = ((X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))))) ◇ X3) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) = (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))))) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := superpose eq9 eq7
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X0) = X2 := superpose eq24 eq23
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ X3))) = X2 := superpose eq9 eq10
  have eq56 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X2 ◇ X4))) = (X0 ◇ (X3 ◇ (((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X0) ◇ X3))) := superpose eq9 eq24
  have eq75 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X2 ◇ X4))) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq7 eq56
  have eq92 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3))) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq33 eq9
  have eq101 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3))) = (X0 ◇ (X0 ◇ X2)) := superpose eq92 eq12
  have eq102 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq101 eq11
  have eq129 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq102 eq33
  have eq223 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))))) = X0 := superpose eq17 eq24
  have eq476 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X2) = X1 := superpose eq75 eq7
  have eq477 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3)))) = X1 := superpose eq75 eq24
  have eq491 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) ◇ X3) = X1 := superpose eq75 eq33
  have eq1282 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq491 eq129
  have eq1529 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq1282 eq33
  have eq2027 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X0 ◇ (X6 ◇ ((X2 ◇ X0) ◇ X6))))) ◇ (X5 ◇ (X4 ◇ X5))) = ((X5 ◇ (X4 ◇ X5)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X4 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))))) := superpose eq17 eq19
  have eq2888 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1529 eq24
  have eq2980 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1))) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1)))) ◇ X2))) := superpose eq14 eq47
  have eq3056 (X0 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq2888 eq7
  have eq3061 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := superpose eq2888 eq477
  have eq3077 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) = X2 := superpose eq2888 eq476
  have eq3269 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq33 eq3056
  have eq3276 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq3056 eq33
  have eq3514 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq3061 eq29
  have eq3533 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq3514 eq3269
  have eq3535 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ X2))) := superpose eq3533 eq2980
  have eq3541 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := superpose eq3533 eq223
  have eq3542 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X5 ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X0 ◇ (X6 ◇ ((X2 ◇ X0) ◇ X6))))) ◇ (X5 ◇ (X4 ◇ X5))) = ((X5 ◇ (X4 ◇ X5)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq3533 eq2027
  have eq4475 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))))) := superpose eq3533 eq3535
  have eq4476 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq3533 eq4475
  have eq4477 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq3533 eq4476
  have eq4478 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq4477 eq3276
  have eq4493 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2)) = X0 := superpose eq3533 eq3541
  have eq4494 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq3533 eq4493
  have eq4495 (X0 X1 X2 X4 X5 X6 : G) : (((X5 ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X0 ◇ (X6 ◇ ((X2 ◇ X0) ◇ X6))))) ◇ (X5 ◇ (X4 ◇ X5))) = ((X5 ◇ (X4 ◇ X5)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X4)) := superpose eq3533 eq3542
  have eq4496 (X0 X2 X4 X5 X6 : G) : (((X5 ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X0 ◇ (X6 ◇ ((X2 ◇ X0) ◇ X6))))) ◇ (X5 ◇ (X4 ◇ X5))) = ((X5 ◇ (X4 ◇ X5)) ◇ ((X0 ◇ X2) ◇ X4)) := superpose eq3533 eq4495
  have eq4497 (X0 X2 X4 X6 : G) : (X4 ◇ ((X0 ◇ X2) ◇ X4)) = ((X4 ◇ (X0 ◇ (X0 ◇ (X6 ◇ ((X2 ◇ X0) ◇ X6))))) ◇ X4) := superpose eq3533 eq4496
  have eq4498 (X0 X2 X4 : G) : (X4 ◇ ((X0 ◇ X2) ◇ X4)) = ((X4 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X4) := superpose eq3533 eq4497
  have eq4499 (X0 X2 X4 : G) : (X4 ◇ ((X0 ◇ X2) ◇ X4)) = ((X4 ◇ (X0 ◇ X2)) ◇ X4) := superpose eq3533 eq4498
  have eq4500 (X0 X2 X4 : G) : (X0 ◇ X2) = ((X4 ◇ (X0 ◇ X2)) ◇ X4) := superpose eq3533 eq4499
  have eq4501 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq4500 eq4478
  have eq4517 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X1) = X2 := superpose eq4501 eq3077
  have eq4521 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = X2 := superpose eq4500 eq4517
  have eq4522 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq3533 eq4521
  have eq4524 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq4522 eq4494
  have eq4534 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq4522 eq4524
  have eq4540 (X0 X1 : G) : X0 = X1 := superpose eq4534 eq4522
  have eq4554 (X0 : G) : sK0 ≠ X0 := superpose eq4540 eq8
  subsumption eq4554 eq4540


@[equational_result]
theorem Equation30661_implies_Equation2 (G : Type*) [Magma G] (h : Equation30661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30663_implies_Equation2 (G : Type*) [Magma G] (h : Equation30663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation30664_implies_Equation2 (G : Type*) [Magma G] (h : Equation30664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ X0)) ◇ X4) = X2 := superpose eq7 eq7
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X2) = X0 := superpose eq20 eq7
  have eq36 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X0 := superpose eq20 eq25
  have eq37 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq20 eq36
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation30665_implies_Equation2 (G : Type*) [Magma G] (h : Equation30665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation30666_implies_Equation2 (G : Type*) [Magma G] (h : Equation30666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30668_implies_Equation2 (G : Type*) [Magma G] (h : Equation30668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq54 eq23


@[equational_result]
theorem Equation30669_implies_Equation2 (G : Type*) [Magma G] (h : Equation30669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation30670_implies_Equation2 (G : Type*) [Magma G] (h : Equation30670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30674_implies_Equation2 (G : Type*) [Magma G] (h : Equation30674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30677_implies_Equation2 (G : Type*) [Magma G] (h : Equation30677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq61 eq11


@[equational_result]
theorem Equation30678_implies_Equation2 (G : Type*) [Magma G] (h : Equation30678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30680_implies_Equation2 (G : Type*) [Magma G] (h : Equation30680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0)) ◇ X1) = X4 := superpose eq7 eq7
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq90 eq24


@[equational_result]
theorem Equation30681_implies_Equation2 (G : Type*) [Magma G] (h : Equation30681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation30682_implies_Equation2 (G : Type*) [Magma G] (h : Equation30682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation30683_implies_Equation2 (G : Type*) [Magma G] (h : Equation30683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30685_implies_Equation2 (G : Type*) [Magma G] (h : Equation30685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation30686_implies_Equation2 (G : Type*) [Magma G] (h : Equation30686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30687_implies_Equation2 (G : Type*) [Magma G] (h : Equation30687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30688_implies_Equation2 (G : Type*) [Magma G] (h : Equation30688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30690_implies_Equation2 (G : Type*) [Magma G] (h : Equation30690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation30691_implies_Equation2 (G : Type*) [Magma G] (h : Equation30691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq76 eq18


@[equational_result]
theorem Equation30692_implies_Equation2 (G : Type*) [Magma G] (h : Equation30692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation30693_implies_Equation2 (G : Type*) [Magma G] (h : Equation30693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30695_implies_Equation2 (G : Type*) [Magma G] (h : Equation30695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation30696_implies_Equation2 (G : Type*) [Magma G] (h : Equation30696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30697_implies_Equation2 (G : Type*) [Magma G] (h : Equation30697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq64 eq12


@[equational_result]
theorem Equation30698_implies_Equation2 (G : Type*) [Magma G] (h : Equation30698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30700_implies_Equation2 (G : Type*) [Magma G] (h : Equation30700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation30701_implies_Equation2 (G : Type*) [Magma G] (h : Equation30701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation30702_implies_Equation2 (G : Type*) [Magma G] (h : Equation30702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30703_implies_Equation2 (G : Type*) [Magma G] (h : Equation30703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30705_implies_Equation2 (G : Type*) [Magma G] (h : Equation30705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation30706_implies_Equation2 (G : Type*) [Magma G] (h : Equation30706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30707_implies_Equation2 (G : Type*) [Magma G] (h : Equation30707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30708_implies_Equation2 (G : Type*) [Magma G] (h : Equation30708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30709_implies_Equation2 (G : Type*) [Magma G] (h : Equation30709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X9 : G) : (X0 ◇ X9) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30711_implies_Equation2 (G : Type*) [Magma G] (h : Equation30711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq50 eq14


@[equational_result]
theorem Equation30713_implies_Equation2 (G : Type*) [Magma G] (h : Equation30713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30715_implies_Equation2 (G : Type*) [Magma G] (h : Equation30715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation30717_implies_Equation2 (G : Type*) [Magma G] (h : Equation30717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30719_implies_Equation2 (G : Type*) [Magma G] (h : Equation30719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq53 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (X2 ◇ ((X3 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) ◇ X2)) := superpose eq10 eq16
  have eq58 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X2) := superpose eq16 eq16
  have eq59 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X3 := superpose eq10 eq16
  have eq112 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X1)) = X0 := superpose eq7 eq58
  have eq169 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq112 eq53
  have eq183 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X0) = X3 := superpose eq169 eq59
  have eq247 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq169 eq183
  have eq259 (X0 X2 : G) : X0 = X2 := superpose eq247 eq247
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq259 eq8
  subsumption eq292 eq259


@[equational_result]
theorem Equation30720_implies_Equation2 (G : Type*) [Magma G] (h : Equation30720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq28 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X0 := superpose eq28 eq7
  have eq66 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq15
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq66 eq45
  have eq79 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq66 eq68
  have eq92 (X0 X2 : G) : X0 = X2 := superpose eq79 eq79
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq94 eq92


@[equational_result]
theorem Equation30721_implies_Equation2 (G : Type*) [Magma G] (h : Equation30721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30723_implies_Equation2 (G : Type*) [Magma G] (h : Equation30723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation30724_implies_Equation2 (G : Type*) [Magma G] (h : Equation30724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) ◇ (X4 ◇ (X0 ◇ X5))) ◇ X4) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X4)) = ((X1 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq7 eq7
  have eq59 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X5))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X6) = X4 := superpose eq10 eq9
  have eq60 (X0 X2 X3 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X3)) := superpose eq7 eq9
  have eq79 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X5)))) ◇ X6) = X4 := superpose eq60 eq59
  have eq107 (X0 X1 X2 X3 X4 X6 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X6) = X4 := superpose eq60 eq79
  have eq108 (X0 X3 X4 X6 : G) : ((X0 ◇ X3) ◇ X6) = X4 := superpose eq60 eq107
  have eq113 (X0 X4 : G) : X0 = X4 := superpose eq108 eq108
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq113 eq8
  subsumption eq122 eq113


@[equational_result]
theorem Equation30725_implies_Equation2 (G : Type*) [Magma G] (h : Equation30725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq72 eq15


@[equational_result]
theorem Equation30726_implies_Equation2 (G : Type*) [Magma G] (h : Equation30726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) ◇ (X4 ◇ (X0 ◇ X6))) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30728_implies_Equation2 (G : Type*) [Magma G] (h : Equation30728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation30730_implies_Equation2 (G : Type*) [Magma G] (h : Equation30730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation30732_implies_Equation2 (G : Type*) [Magma G] (h : Equation30732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30733_implies_Equation2 (G : Type*) [Magma G] (h : Equation30733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30734_implies_Equation2 (G : Type*) [Magma G] (h : Equation30734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30736_implies_Equation2 (G : Type*) [Magma G] (h : Equation30736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30737_implies_Equation2 (G : Type*) [Magma G] (h : Equation30737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30738_implies_Equation2 (G : Type*) [Magma G] (h : Equation30738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30740_implies_Equation2 (G : Type*) [Magma G] (h : Equation30740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30741_implies_Equation2 (G : Type*) [Magma G] (h : Equation30741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30742_implies_Equation2 (G : Type*) [Magma G] (h : Equation30742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30743_implies_Equation2 (G : Type*) [Magma G] (h : Equation30743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30747_implies_Equation2 (G : Type*) [Magma G] (h : Equation30747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X3 ◇ (X0 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30749_implies_Equation2 (G : Type*) [Magma G] (h : Equation30749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30750_implies_Equation2 (G : Type*) [Magma G] (h : Equation30750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30751_implies_Equation2 (G : Type*) [Magma G] (h : Equation30751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30753_implies_Equation2 (G : Type*) [Magma G] (h : Equation30753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30754_implies_Equation2 (G : Type*) [Magma G] (h : Equation30754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30755_implies_Equation2 (G : Type*) [Magma G] (h : Equation30755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30757_implies_Equation2 (G : Type*) [Magma G] (h : Equation30757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30758_implies_Equation2 (G : Type*) [Magma G] (h : Equation30758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30759_implies_Equation2 (G : Type*) [Magma G] (h : Equation30759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30760_implies_Equation2 (G : Type*) [Magma G] (h : Equation30760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30762_implies_Equation2 (G : Type*) [Magma G] (h : Equation30762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation30763_implies_Equation2 (G : Type*) [Magma G] (h : Equation30763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation30764_implies_Equation2 (G : Type*) [Magma G] (h : Equation30764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation30765_implies_Equation2 (G : Type*) [Magma G] (h : Equation30765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X4 ◇ (X0 ◇ X6))) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation30767_implies_Equation2 (G : Type*) [Magma G] (h : Equation30767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30768_implies_Equation2 (G : Type*) [Magma G] (h : Equation30768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30769_implies_Equation2 (G : Type*) [Magma G] (h : Equation30769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30770_implies_Equation2 (G : Type*) [Magma G] (h : Equation30770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30772_implies_Equation2 (G : Type*) [Magma G] (h : Equation30772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30773_implies_Equation2 (G : Type*) [Magma G] (h : Equation30773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30774_implies_Equation2 (G : Type*) [Magma G] (h : Equation30774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30775_implies_Equation2 (G : Type*) [Magma G] (h : Equation30775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30777_implies_Equation2 (G : Type*) [Magma G] (h : Equation30777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30778_implies_Equation2 (G : Type*) [Magma G] (h : Equation30778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30779_implies_Equation2 (G : Type*) [Magma G] (h : Equation30779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30780_implies_Equation2 (G : Type*) [Magma G] (h : Equation30780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30782_implies_Equation2 (G : Type*) [Magma G] (h : Equation30782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30783_implies_Equation2 (G : Type*) [Magma G] (h : Equation30783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30784_implies_Equation2 (G : Type*) [Magma G] (h : Equation30784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30785_implies_Equation2 (G : Type*) [Magma G] (h : Equation30785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30786_implies_Equation2 (G : Type*) [Magma G] (h : Equation30786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30789_implies_Equation2 (G : Type*) [Magma G] (h : Equation30789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation30790_implies_Equation2 (G : Type*) [Magma G] (h : Equation30790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30792_implies_Equation2 (G : Type*) [Magma G] (h : Equation30792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X2))) ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2)) = X0 := superpose eq7 eq10
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X2) := superpose eq10 eq7
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq55 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq38 eq17
  have eq73 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X2 ◇ X1) ◇ X2) := superpose eq10 eq38
  have eq76 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X0 := superpose eq38 eq7
  have eq88 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq38 eq73
  have eq97 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) := superpose eq88 eq22
  have eq142 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq76 eq97
  have eq157 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq142 eq55
  have eq193 (X0 X3 : G) : X0 = X3 := superpose eq157 eq157
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq207 eq193


@[equational_result]
theorem Equation30794_implies_Equation2 (G : Type*) [Magma G] (h : Equation30794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30796_implies_Equation2 (G : Type*) [Magma G] (h : Equation30796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X3)) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3)))) = X2 := superpose eq7 eq7
  have eq46 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0))) = X3 := superpose eq10 eq11
  have eq51 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq46
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq134 eq59


@[equational_result]
theorem Equation30797_implies_Equation2 (G : Type*) [Magma G] (h : Equation30797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq52 eq12


@[equational_result]
theorem Equation30798_implies_Equation2 (G : Type*) [Magma G] (h : Equation30798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30800_implies_Equation2 (G : Type*) [Magma G] (h : Equation30800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X4))) ◇ (X0 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X4)) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) ◇ X4) = (X1 ◇ X0) := superpose eq7 eq10
  have eq27 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = X2 := superpose eq10 eq7
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq68 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) ◇ X4) = X0 := superpose eq7 eq52
  have eq120 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq68 eq15
  have eq124 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = X2 := superpose eq120 eq27
  have eq172 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq120 eq124
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq172 eq172
  have eq192 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq192 eq173


@[equational_result]
theorem Equation30801_implies_Equation2 (G : Type*) [Magma G] (h : Equation30801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation30802_implies_Equation2 (G : Type*) [Magma G] (h : Equation30802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation30803_implies_Equation2 (G : Type*) [Magma G] (h : Equation30803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30807_implies_Equation2 (G : Type*) [Magma G] (h : Equation30807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30809_implies_Equation2 (G : Type*) [Magma G] (h : Equation30809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30810_implies_Equation2 (G : Type*) [Magma G] (h : Equation30810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30811_implies_Equation2 (G : Type*) [Magma G] (h : Equation30811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30813_implies_Equation2 (G : Type*) [Magma G] (h : Equation30813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30814_implies_Equation2 (G : Type*) [Magma G] (h : Equation30814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30815_implies_Equation2 (G : Type*) [Magma G] (h : Equation30815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30817_implies_Equation2 (G : Type*) [Magma G] (h : Equation30817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30818_implies_Equation2 (G : Type*) [Magma G] (h : Equation30818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30819_implies_Equation2 (G : Type*) [Magma G] (h : Equation30819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30820_implies_Equation2 (G : Type*) [Magma G] (h : Equation30820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30823_implies_Equation2 (G : Type*) [Magma G] (h : Equation30823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq42 eq11


@[equational_result]
theorem Equation30824_implies_Equation2 (G : Type*) [Magma G] (h : Equation30824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30826_implies_Equation2 (G : Type*) [Magma G] (h : Equation30826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30827_implies_Equation2 (G : Type*) [Magma G] (h : Equation30827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation30828_implies_Equation2 (G : Type*) [Magma G] (h : Equation30828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30830_implies_Equation2 (G : Type*) [Magma G] (h : Equation30830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30831_implies_Equation2 (G : Type*) [Magma G] (h : Equation30831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30832_implies_Equation2 (G : Type*) [Magma G] (h : Equation30832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30834_implies_Equation2 (G : Type*) [Magma G] (h : Equation30834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30835_implies_Equation2 (G : Type*) [Magma G] (h : Equation30835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30836_implies_Equation2 (G : Type*) [Magma G] (h : Equation30836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30837_implies_Equation2 (G : Type*) [Magma G] (h : Equation30837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30839_implies_Equation2 (G : Type*) [Magma G] (h : Equation30839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation30840_implies_Equation2 (G : Type*) [Magma G] (h : Equation30840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30841_implies_Equation2 (G : Type*) [Magma G] (h : Equation30841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30842_implies_Equation2 (G : Type*) [Magma G] (h : Equation30842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation30844_implies_Equation2 (G : Type*) [Magma G] (h : Equation30844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30845_implies_Equation2 (G : Type*) [Magma G] (h : Equation30845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30846_implies_Equation2 (G : Type*) [Magma G] (h : Equation30846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30847_implies_Equation2 (G : Type*) [Magma G] (h : Equation30847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30849_implies_Equation2 (G : Type*) [Magma G] (h : Equation30849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30850_implies_Equation2 (G : Type*) [Magma G] (h : Equation30850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30851_implies_Equation2 (G : Type*) [Magma G] (h : Equation30851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30852_implies_Equation2 (G : Type*) [Magma G] (h : Equation30852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30854_implies_Equation2 (G : Type*) [Magma G] (h : Equation30854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30855_implies_Equation2 (G : Type*) [Magma G] (h : Equation30855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30856_implies_Equation2 (G : Type*) [Magma G] (h : Equation30856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30857_implies_Equation2 (G : Type*) [Magma G] (h : Equation30857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30859_implies_Equation2 (G : Type*) [Magma G] (h : Equation30859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30860_implies_Equation2 (G : Type*) [Magma G] (h : Equation30860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30861_implies_Equation2 (G : Type*) [Magma G] (h : Equation30861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30862_implies_Equation2 (G : Type*) [Magma G] (h : Equation30862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30863_implies_Equation2 (G : Type*) [Magma G] (h : Equation30863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30865_implies_Equation2 (G : Type*) [Magma G] (h : Equation30865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation30866_implies_Equation2 (G : Type*) [Magma G] (h : Equation30866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation30867_implies_Equation2 (G : Type*) [Magma G] (h : Equation30867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30868_implies_Equation2 (G : Type*) [Magma G] (h : Equation30868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30870_implies_Equation2 (G : Type*) [Magma G] (h : Equation30870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation30871_implies_Equation2 (G : Type*) [Magma G] (h : Equation30871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation30872_implies_Equation2 (G : Type*) [Magma G] (h : Equation30872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq72 eq15


@[equational_result]
theorem Equation30873_implies_Equation2 (G : Type*) [Magma G] (h : Equation30873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30875_implies_Equation2 (G : Type*) [Magma G] (h : Equation30875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation30876_implies_Equation2 (G : Type*) [Magma G] (h : Equation30876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation30877_implies_Equation2 (G : Type*) [Magma G] (h : Equation30877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq60 eq12


@[equational_result]
theorem Equation30878_implies_Equation2 (G : Type*) [Magma G] (h : Equation30878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30880_implies_Equation2 (G : Type*) [Magma G] (h : Equation30880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation30881_implies_Equation2 (G : Type*) [Magma G] (h : Equation30881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation30882_implies_Equation2 (G : Type*) [Magma G] (h : Equation30882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30883_implies_Equation2 (G : Type*) [Magma G] (h : Equation30883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30885_implies_Equation2 (G : Type*) [Magma G] (h : Equation30885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation30886_implies_Equation2 (G : Type*) [Magma G] (h : Equation30886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation30887_implies_Equation2 (G : Type*) [Magma G] (h : Equation30887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30888_implies_Equation2 (G : Type*) [Magma G] (h : Equation30888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30889_implies_Equation2 (G : Type*) [Magma G] (h : Equation30889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X9 : G) : (X0 ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30891_implies_Equation2 (G : Type*) [Magma G] (h : Equation30891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation30892_implies_Equation2 (G : Type*) [Magma G] (h : Equation30892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X2) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X4 ◇ X0)) ◇ X4) = X1 := superpose eq7 eq7
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq9 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation30893_implies_Equation2 (G : Type*) [Magma G] (h : Equation30893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation30894_implies_Equation2 (G : Type*) [Magma G] (h : Equation30894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30896_implies_Equation2 (G : Type*) [Magma G] (h : Equation30896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30897_implies_Equation2 (G : Type*) [Magma G] (h : Equation30897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30898_implies_Equation2 (G : Type*) [Magma G] (h : Equation30898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30899_implies_Equation2 (G : Type*) [Magma G] (h : Equation30899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30901_implies_Equation2 (G : Type*) [Magma G] (h : Equation30901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30902_implies_Equation2 (G : Type*) [Magma G] (h : Equation30902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30903_implies_Equation2 (G : Type*) [Magma G] (h : Equation30903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30904_implies_Equation2 (G : Type*) [Magma G] (h : Equation30904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30906_implies_Equation2 (G : Type*) [Magma G] (h : Equation30906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30907_implies_Equation2 (G : Type*) [Magma G] (h : Equation30907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30908_implies_Equation2 (G : Type*) [Magma G] (h : Equation30908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30909_implies_Equation2 (G : Type*) [Magma G] (h : Equation30909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30911_implies_Equation2 (G : Type*) [Magma G] (h : Equation30911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30912_implies_Equation2 (G : Type*) [Magma G] (h : Equation30912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30913_implies_Equation2 (G : Type*) [Magma G] (h : Equation30913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30914_implies_Equation2 (G : Type*) [Magma G] (h : Equation30914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30915_implies_Equation2 (G : Type*) [Magma G] (h : Equation30915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30917_implies_Equation2 (G : Type*) [Magma G] (h : Equation30917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0)) ◇ X1) = X4 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq9 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq55 eq36


@[equational_result]
theorem Equation30918_implies_Equation2 (G : Type*) [Magma G] (h : Equation30918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation30919_implies_Equation2 (G : Type*) [Magma G] (h : Equation30919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation30920_implies_Equation2 (G : Type*) [Magma G] (h : Equation30920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30922_implies_Equation2 (G : Type*) [Magma G] (h : Equation30922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30923_implies_Equation2 (G : Type*) [Magma G] (h : Equation30923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30924_implies_Equation2 (G : Type*) [Magma G] (h : Equation30924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30925_implies_Equation2 (G : Type*) [Magma G] (h : Equation30925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30927_implies_Equation2 (G : Type*) [Magma G] (h : Equation30927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30928_implies_Equation2 (G : Type*) [Magma G] (h : Equation30928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30929_implies_Equation2 (G : Type*) [Magma G] (h : Equation30929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30930_implies_Equation2 (G : Type*) [Magma G] (h : Equation30930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30932_implies_Equation2 (G : Type*) [Magma G] (h : Equation30932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30933_implies_Equation2 (G : Type*) [Magma G] (h : Equation30933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30934_implies_Equation2 (G : Type*) [Magma G] (h : Equation30934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30935_implies_Equation2 (G : Type*) [Magma G] (h : Equation30935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30937_implies_Equation2 (G : Type*) [Magma G] (h : Equation30937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30938_implies_Equation2 (G : Type*) [Magma G] (h : Equation30938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30939_implies_Equation2 (G : Type*) [Magma G] (h : Equation30939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30940_implies_Equation2 (G : Type*) [Magma G] (h : Equation30940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30941_implies_Equation2 (G : Type*) [Magma G] (h : Equation30941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30943_implies_Equation2 (G : Type*) [Magma G] (h : Equation30943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation30944_implies_Equation2 (G : Type*) [Magma G] (h : Equation30944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation30945_implies_Equation2 (G : Type*) [Magma G] (h : Equation30945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation30946_implies_Equation2 (G : Type*) [Magma G] (h : Equation30946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30948_implies_Equation2 (G : Type*) [Magma G] (h : Equation30948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30949_implies_Equation2 (G : Type*) [Magma G] (h : Equation30949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30950_implies_Equation2 (G : Type*) [Magma G] (h : Equation30950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation30951_implies_Equation2 (G : Type*) [Magma G] (h : Equation30951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30953_implies_Equation2 (G : Type*) [Magma G] (h : Equation30953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30954_implies_Equation2 (G : Type*) [Magma G] (h : Equation30954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30955_implies_Equation2 (G : Type*) [Magma G] (h : Equation30955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30956_implies_Equation2 (G : Type*) [Magma G] (h : Equation30956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30958_implies_Equation2 (G : Type*) [Magma G] (h : Equation30958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30959_implies_Equation2 (G : Type*) [Magma G] (h : Equation30959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30960_implies_Equation2 (G : Type*) [Magma G] (h : Equation30960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation30961_implies_Equation2 (G : Type*) [Magma G] (h : Equation30961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30963_implies_Equation2 (G : Type*) [Magma G] (h : Equation30963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30964_implies_Equation2 (G : Type*) [Magma G] (h : Equation30964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30965_implies_Equation2 (G : Type*) [Magma G] (h : Equation30965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30966_implies_Equation2 (G : Type*) [Magma G] (h : Equation30966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30967_implies_Equation2 (G : Type*) [Magma G] (h : Equation30967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30969_implies_Equation2 (G : Type*) [Magma G] (h : Equation30969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation30970_implies_Equation2 (G : Type*) [Magma G] (h : Equation30970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation30971_implies_Equation2 (G : Type*) [Magma G] (h : Equation30971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30972_implies_Equation2 (G : Type*) [Magma G] (h : Equation30972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30973_implies_Equation2 (G : Type*) [Magma G] (h : Equation30973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation30975_implies_Equation2 (G : Type*) [Magma G] (h : Equation30975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30976_implies_Equation2 (G : Type*) [Magma G] (h : Equation30976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30977_implies_Equation2 (G : Type*) [Magma G] (h : Equation30977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30978_implies_Equation2 (G : Type*) [Magma G] (h : Equation30978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30979_implies_Equation2 (G : Type*) [Magma G] (h : Equation30979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30981_implies_Equation2 (G : Type*) [Magma G] (h : Equation30981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30982_implies_Equation2 (G : Type*) [Magma G] (h : Equation30982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30983_implies_Equation2 (G : Type*) [Magma G] (h : Equation30983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30984_implies_Equation2 (G : Type*) [Magma G] (h : Equation30984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30985_implies_Equation2 (G : Type*) [Magma G] (h : Equation30985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30987_implies_Equation2 (G : Type*) [Magma G] (h : Equation30987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30988_implies_Equation2 (G : Type*) [Magma G] (h : Equation30988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30989_implies_Equation2 (G : Type*) [Magma G] (h : Equation30989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30990_implies_Equation2 (G : Type*) [Magma G] (h : Equation30990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30991_implies_Equation2 (G : Type*) [Magma G] (h : Equation30991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30993_implies_Equation2 (G : Type*) [Magma G] (h : Equation30993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30994_implies_Equation2 (G : Type*) [Magma G] (h : Equation30994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30995_implies_Equation2 (G : Type*) [Magma G] (h : Equation30995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30996_implies_Equation2 (G : Type*) [Magma G] (h : Equation30996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation30997_implies_Equation2 (G : Type*) [Magma G] (h : Equation30997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation30999_implies_Equation2 (G : Type*) [Magma G] (h : Equation30999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31000_implies_Equation2 (G : Type*) [Magma G] (h : Equation31000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31001_implies_Equation2 (G : Type*) [Magma G] (h : Equation31001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31002_implies_Equation2 (G : Type*) [Magma G] (h : Equation31002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31003_implies_Equation2 (G : Type*) [Magma G] (h : Equation31003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31004_implies_Equation2 (G : Type*) [Magma G] (h : Equation31004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31210_implies_Equation2 (G : Type*) [Magma G] (h : Equation31210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation31213_implies_Equation2 (G : Type*) [Magma G] (h : Equation31213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq66 eq14


@[equational_result]
theorem Equation31215_implies_Equation2 (G : Type*) [Magma G] (h : Equation31215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq10 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq18
  have eq108 (X0 X3 : G) : X0 = X3 := superpose eq7 eq37
  have eq212 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq212 eq108


@[equational_result]
theorem Equation31216_implies_Equation2 (G : Type*) [Magma G] (h : Equation31216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation31217_implies_Equation2 (G : Type*) [Magma G] (h : Equation31217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation31220_implies_Equation2 (G : Type*) [Magma G] (h : Equation31220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation31223_implies_Equation2 (G : Type*) [Magma G] (h : Equation31223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq70 eq13


@[equational_result]
theorem Equation31225_implies_Equation2 (G : Type*) [Magma G] (h : Equation31225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X3) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)))) = X1 := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq18
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq166 eq60


@[equational_result]
theorem Equation31227_implies_Equation2 (G : Type*) [Magma G] (h : Equation31227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq73 eq13


@[equational_result]
theorem Equation31229_implies_Equation2 (G : Type*) [Magma G] (h : Equation31229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq9
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq94 eq62


@[equational_result]
theorem Equation31230_implies_Equation2 (G : Type*) [Magma G] (h : Equation31230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation31231_implies_Equation2 (G : Type*) [Magma G] (h : Equation31231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31233_implies_Equation2 (G : Type*) [Magma G] (h : Equation31233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) = X1 := superpose eq9 eq9
  have eq97 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq12
  have eq116 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq97 eq7
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq9 eq116
  have eq212 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq212 eq119


@[equational_result]
theorem Equation31235_implies_Equation2 (G : Type*) [Magma G] (h : Equation31235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31237_implies_Equation2 (G : Type*) [Magma G] (h : Equation31237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq33 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq34 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq10
  have eq38 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq10 eq7
  have eq39 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq38 eq34
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) = X0 := superpose eq39 eq7
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq39 eq33
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq39 eq46
  have eq108 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq60 eq72
  have eq115 (X0 X2 : G) : X0 = X2 := superpose eq108 eq108
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq117 eq115


@[equational_result]
theorem Equation31238_implies_Equation2 (G : Type*) [Magma G] (h : Equation31238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq54 eq11


@[equational_result]
theorem Equation31239_implies_Equation2 (G : Type*) [Magma G] (h : Equation31239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31241_implies_Equation2 (G : Type*) [Magma G] (h : Equation31241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X4 ◇ X5)))) = X1 := superpose eq7 eq7
  have eq135 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq11 eq11
  have eq193 (X0 X3 : G) : X0 = X3 := superpose eq7 eq135
  have eq248 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq248 eq193


@[equational_result]
theorem Equation31242_implies_Equation2 (G : Type*) [Magma G] (h : Equation31242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq63 eq12


@[equational_result]
theorem Equation31243_implies_Equation2 (G : Type*) [Magma G] (h : Equation31243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31244_implies_Equation2 (G : Type*) [Magma G] (h : Equation31244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31247_implies_Equation2 (G : Type*) [Magma G] (h : Equation31247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation31250_implies_Equation2 (G : Type*) [Magma G] (h : Equation31250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq39 eq12


@[equational_result]
theorem Equation31252_implies_Equation2 (G : Type*) [Magma G] (h : Equation31252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X1 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) = ((X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq7 eq9
  have eq18 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq15 eq7
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = ((X1 ◇ ((((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) ◇ X0)) ◇ X1) := superpose eq15 eq10
  have eq27 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) = X1 := superpose eq18 eq18
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) ◇ X1) = (X1 ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2))) := superpose eq18 eq15
  have eq31 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose eq15 eq15
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2))) = (((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X1) ◇ X1) := superpose eq15 eq28
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2))) := superpose eq18 eq33
  have eq55 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := superpose eq15 eq34
  have eq78 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ ((X0 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0))) := superpose eq15 eq31
  have eq94 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq18 eq78
  have eq108 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ X2)) := superpose eq18 eq94
  have eq111 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3)) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq94 eq94
  have eq112 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) := superpose eq15 eq94
  have eq116 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X1)) ◇ (X2 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X1)))) ◇ X2) = (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) := superpose eq20 eq94
  have eq121 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2))) = ((X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq34 eq94
  have eq123 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X0) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) := superpose eq94 eq94
  have eq125 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq15 eq94
  have eq133 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X1 := superpose eq94 eq18
  have eq134 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X2)))) := superpose eq94 eq34
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq94 eq27
  have eq163 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = X1 := superpose eq18 eq112
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2)) := superpose eq125 eq108
  have eq195 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq18 eq133
  have eq205 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq94 eq133
  have eq206 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose eq18 eq133
  have eq240 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) = (((X2 ◇ (X2 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X1))) ◇ X2) ◇ X2) := superpose eq206 eq116
  have eq246 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) = (((X2 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) := superpose eq195 eq240
  have eq247 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3)) = X2 := superpose eq18 eq246
  have eq249 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq247 eq205
  have eq250 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq247 eq123
  have eq270 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq247 eq168
  have eq272 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq247 eq121
  have eq275 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq247 eq34
  have eq303 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq272 eq134
  have eq305 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq275 eq111
  have eq311 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq275 eq270
  have eq315 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq275 eq303
  have eq317 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq275 eq139
  have eq318 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := superpose eq275 eq55
  have eq324 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq275 eq250
  have eq326 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq275 eq18
  have eq330 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X1)) = ((X2 ◇ X0) ◇ X2) := superpose eq275 eq94
  have eq341 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq275 eq305
  have eq348 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose eq275 eq311
  have eq354 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq275 eq315
  have eq355 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq275 eq354
  have eq358 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq275 eq317
  have eq359 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq275 eq318
  have eq371 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq330 eq341
  have eq377 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq324 eq371
  have eq380 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq377 eq358
  have eq381 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq330 eq380
  have eq382 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq249 eq381
  have eq385 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq382 eq348
  have eq389 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq382 eq355
  have eq401 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq389 eq385
  have eq403 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq401 eq326
  have eq406 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)))) := superpose eq401 eq359
  have eq412 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq403 eq163
  have eq417 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq412 eq406
  have eq419 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq417 eq403
  have eq424 (X0 X2 : G) : X0 = X2 := superpose eq419 eq419
  have eq426 (X0 : G) : sK0 ≠ X0 := superpose eq424 eq8
  subsumption eq426 eq424


@[equational_result]
theorem Equation31254_implies_Equation2 (G : Type*) [Magma G] (h : Equation31254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation31257_implies_Equation2 (G : Type*) [Magma G] (h : Equation31257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation31260_implies_Equation2 (G : Type*) [Magma G] (h : Equation31260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq74 eq14


@[equational_result]
theorem Equation31262_implies_Equation2 (G : Type*) [Magma G] (h : Equation31262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((X1 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X5))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) = (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X3))) = (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq7
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = X1 := superpose eq25 eq24
  have eq58 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4))) = X0 := superpose eq9 eq25
  have eq83 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = X2 := superpose eq25 eq33
  have eq86 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X4))) = (((X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)))) ◇ X0) ◇ X0) := superpose eq9 eq33
  have eq130 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X4))) := superpose eq83 eq86
  have eq134 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) = X0 := superpose eq130 eq29
  have eq135 (X0 X1 X3 X5 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = ((((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X5))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) := superpose eq130 eq13
  have eq141 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) := superpose eq130 eq135
  have eq142 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq134 eq141
  have eq143 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq142 eq7
  have eq150 (X0 X1 X2 X4 : G) : (X0 ◇ ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) ◇ (X0 ◇ X4))) = X0 := superpose eq142 eq58
  have eq191 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq142 eq150
  have eq196 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq191 eq143
  have eq217 (X0 X2 : G) : X0 = X2 := superpose eq196 eq196
  have eq219 (X0 : G) : sK0 ≠ X0 := superpose eq217 eq8
  subsumption eq219 eq217


@[equational_result]
theorem Equation31264_implies_Equation2 (G : Type*) [Magma G] (h : Equation31264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation31266_implies_Equation2 (G : Type*) [Magma G] (h : Equation31266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq10
  have eq42 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)) = X0 := superpose eq7 eq12
  have eq152 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq42 eq42
  have eq192 (X0 X3 : G) : X0 = X3 := superpose eq10 eq152
  have eq299 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq299 eq192


@[equational_result]
theorem Equation31268_implies_Equation2 (G : Type*) [Magma G] (h : Equation31268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31270_implies_Equation2 (G : Type*) [Magma G] (h : Equation31270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq35 eq10
  have eq117 (X0 X3 : G) : X0 = X3 := superpose eq7 eq72
  have eq263 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq263 eq117


@[equational_result]
theorem Equation31272_implies_Equation2 (G : Type*) [Magma G] (h : Equation31272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31276_implies_Equation2 (G : Type*) [Magma G] (h : Equation31276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31278_implies_Equation2 (G : Type*) [Magma G] (h : Equation31278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((X1 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X1) := superpose eq7 eq7
  have eq44 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X3))) = X0 := superpose eq7 eq9
  have eq75 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq44 eq44
  have eq129 (X0 X4 : G) : X0 = X4 := superpose eq7 eq75
  have eq246 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq246 eq129


@[equational_result]
theorem Equation31279_implies_Equation2 (G : Type*) [Magma G] (h : Equation31279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X2) = X1 := superpose eq7 eq7
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq84 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq179 eq84


@[equational_result]
theorem Equation31280_implies_Equation2 (G : Type*) [Magma G] (h : Equation31280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq10 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq155 eq41


@[equational_result]
theorem Equation31281_implies_Equation2 (G : Type*) [Magma G] (h : Equation31281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31283_implies_Equation2 (G : Type*) [Magma G] (h : Equation31283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) = X2 := superpose eq10 eq7
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq16
  have eq76 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq169 eq76


@[equational_result]
theorem Equation31284_implies_Equation2 (G : Type*) [Magma G] (h : Equation31284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation31285_implies_Equation2 (G : Type*) [Magma G] (h : Equation31285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation31287_implies_Equation2 (G : Type*) [Magma G] (h : Equation31287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X2))) = ((X1 ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X2))) ◇ X1))) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq7 eq9
  have eq18 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq15 eq7
  have eq29 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq15 eq15
  have eq65 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq15 eq29
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq18 eq65
  have eq141 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ X1) := superpose eq18 eq82
  have eq221 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X2 := superpose eq141 eq18
  have eq282 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq18 eq221
  have eq312 (X0 X2 : G) : X0 = X2 := superpose eq18 eq282
  have eq496 (X0 : G) : sK0 ≠ X0 := superpose eq312 eq8
  subsumption eq496 eq312


@[equational_result]
theorem Equation31289_implies_Equation2 (G : Type*) [Magma G] (h : Equation31289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation31291_implies_Equation2 (G : Type*) [Magma G] (h : Equation31291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq7 eq9
  have eq44 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X4) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) = X3 := superpose eq9 eq10
  have eq58 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq22 eq44
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq7 eq58
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq147 eq59


@[equational_result]
theorem Equation31292_implies_Equation2 (G : Type*) [Magma G] (h : Equation31292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq57 eq11


@[equational_result]
theorem Equation31293_implies_Equation2 (G : Type*) [Magma G] (h : Equation31293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31295_implies_Equation2 (G : Type*) [Magma G] (h : Equation31295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) = ((X1 ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) ◇ X5))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) = ((X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) ◇ X5) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X4) ◇ (X0 ◇ X5)))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq7 eq11
  have eq30 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq22 eq9
  have eq35 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) ◇ X5) ◇ X0)) = ((X6 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))))) ◇ X6) := superpose eq7 eq30
  have eq61 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X3 := superpose eq30 eq11
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) ◇ X5) ◇ X0)) = X2 := superpose eq7 eq35
  have eq80 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) = (X2 ◇ X1) := superpose eq78 eq10
  have eq147 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq11 eq80
  have eq205 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := superpose eq147 eq61
  have eq248 (X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X5))) = X3 := superpose eq147 eq205
  have eq249 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X4)) = X3 := superpose eq147 eq248
  have eq250 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X3 := superpose eq147 eq249
  have eq251 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq147 eq250
  have eq254 (X0 X1 : G) : X0 = X1 := superpose eq147 eq251
  have eq256 (X0 : G) : sK0 ≠ X0 := superpose eq254 eq8
  subsumption eq256 eq254


@[equational_result]
theorem Equation31296_implies_Equation2 (G : Type*) [Magma G] (h : Equation31296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation31297_implies_Equation2 (G : Type*) [Magma G] (h : Equation31297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31298_implies_Equation2 (G : Type*) [Magma G] (h : Equation31298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation31300_implies_Equation2 (G : Type*) [Magma G] (h : Equation31300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq10
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq7 eq22
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq90 eq42


@[equational_result]
theorem Equation31302_implies_Equation2 (G : Type*) [Magma G] (h : Equation31302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation31304_implies_Equation2 (G : Type*) [Magma G] (h : Equation31304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation31306_implies_Equation2 (G : Type*) [Magma G] (h : Equation31306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq76 eq14


@[equational_result]
theorem Equation31310_implies_Equation2 (G : Type*) [Magma G] (h : Equation31310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation31312_implies_Equation2 (G : Type*) [Magma G] (h : Equation31312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq177 eq71


@[equational_result]
theorem Equation31313_implies_Equation2 (G : Type*) [Magma G] (h : Equation31313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X4))) = ((X1 ◇ (X0 ◇ (X1 ◇ X5))) ◇ X3) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq64 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) ◇ X5) = X4 := superpose eq9 eq7
  have eq65 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X3) = ((X4 ◇ X5) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := superpose eq9 eq11
  have eq87 (X1 X3 X4 X5 : G) : ((X1 ◇ X3) ◇ X5) = X4 := superpose eq65 eq64
  have eq96 (X0 X4 : G) : X0 = X4 := superpose eq7 eq87
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq182 eq96


@[equational_result]
theorem Equation31314_implies_Equation2 (G : Type*) [Magma G] (h : Equation31314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq75 eq15


@[equational_result]
theorem Equation31315_implies_Equation2 (G : Type*) [Magma G] (h : Equation31315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X7 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ ((X4 ◇ X5) ◇ X0)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation31318_implies_Equation2 (G : Type*) [Magma G] (h : Equation31318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq53 eq12


@[equational_result]
theorem Equation31319_implies_Equation2 (G : Type*) [Magma G] (h : Equation31319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31323_implies_Equation2 (G : Type*) [Magma G] (h : Equation31323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31326_implies_Equation2 (G : Type*) [Magma G] (h : Equation31326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq65 eq11


@[equational_result]
theorem Equation31327_implies_Equation2 (G : Type*) [Magma G] (h : Equation31327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31329_implies_Equation2 (G : Type*) [Magma G] (h : Equation31329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq23 (X0 X1 X4 : G) : ((X4 ◇ X1) ◇ X4) = X0 := superpose eq7 eq11
  have eq113 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq113 eq8
  subsumption eq239 eq113


@[equational_result]
theorem Equation31330_implies_Equation2 (G : Type*) [Magma G] (h : Equation31330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation31331_implies_Equation2 (G : Type*) [Magma G] (h : Equation31331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation31332_implies_Equation2 (G : Type*) [Magma G] (h : Equation31332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31334_implies_Equation2 (G : Type*) [Magma G] (h : Equation31334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq127 eq45


@[equational_result]
theorem Equation31335_implies_Equation2 (G : Type*) [Magma G] (h : Equation31335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31336_implies_Equation2 (G : Type*) [Magma G] (h : Equation31336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31337_implies_Equation2 (G : Type*) [Magma G] (h : Equation31337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31339_implies_Equation2 (G : Type*) [Magma G] (h : Equation31339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq153 eq49


@[equational_result]
theorem Equation31340_implies_Equation2 (G : Type*) [Magma G] (h : Equation31340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq160 eq43


@[equational_result]
theorem Equation31341_implies_Equation2 (G : Type*) [Magma G] (h : Equation31341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq75 eq15


@[equational_result]
theorem Equation31342_implies_Equation2 (G : Type*) [Magma G] (h : Equation31342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31344_implies_Equation2 (G : Type*) [Magma G] (h : Equation31344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq206 eq72


@[equational_result]
theorem Equation31345_implies_Equation2 (G : Type*) [Magma G] (h : Equation31345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31346_implies_Equation2 (G : Type*) [Magma G] (h : Equation31346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation31347_implies_Equation2 (G : Type*) [Magma G] (h : Equation31347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31349_implies_Equation2 (G : Type*) [Magma G] (h : Equation31349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq75 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq167 eq75


@[equational_result]
theorem Equation31350_implies_Equation2 (G : Type*) [Magma G] (h : Equation31350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq63 eq12


@[equational_result]
theorem Equation31351_implies_Equation2 (G : Type*) [Magma G] (h : Equation31351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation31352_implies_Equation2 (G : Type*) [Magma G] (h : Equation31352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31354_implies_Equation2 (G : Type*) [Magma G] (h : Equation31354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq173 eq53


@[equational_result]
theorem Equation31355_implies_Equation2 (G : Type*) [Magma G] (h : Equation31355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31356_implies_Equation2 (G : Type*) [Magma G] (h : Equation31356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31357_implies_Equation2 (G : Type*) [Magma G] (h : Equation31357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31358_implies_Equation2 (G : Type*) [Magma G] (h : Equation31358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X9 : G) : (X0 ◇ X9) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31361_implies_Equation2 (G : Type*) [Magma G] (h : Equation31361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31364_implies_Equation2 (G : Type*) [Magma G] (h : Equation31364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31366_implies_Equation2 (G : Type*) [Magma G] (h : Equation31366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X3))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = ((X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X0)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4))) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X0))) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4))) = ((X1 ◇ ((X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) ◇ X1) := superpose eq9 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3)))) := superpose eq9 eq10
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X1)) = ((((X3 ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4))) ◇ (X3 ◇ ((X3 ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X1)) ◇ X5))) ◇ ((X3 ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)))) := superpose eq10 eq9
  have eq63 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X4 ◇ ((X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ (((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0)) ◇ X6))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ (X4 ◇ ((X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ (((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0)) ◇ X6)))) = X4 := superpose eq19 eq9
  have eq71 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X0)) = ((((X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X0)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4))) ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))))) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X0)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4)))) := superpose eq7 eq29
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) = ((((X1 ◇ ((X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4))) ◇ (X1 ◇ X5))) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4))))) ◇ ((X1 ◇ ((X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4))) ◇ (X1 ◇ X5)))) := superpose eq9 eq29
  have eq131 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5))) = ((((X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))))) ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5))) ◇ X0)) := superpose eq17 eq29
  have eq133 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5)))) = X0 := superpose eq17 eq9
  have eq147 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5))) = ((((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))))) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) := superpose eq7 eq131
  have eq148 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) = (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)))) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4))) ◇ X5))) := superpose eq33 eq147
  have eq150 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2))) = X0 := superpose eq148 eq133
  have eq151 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2))) = X0 := superpose eq10 eq150
  have eq220 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X0) := superpose eq151 eq7
  have eq232 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) = (((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) ◇ X4))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) := superpose eq151 eq7
  have eq251 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq220
  have eq252 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq251 eq7
  have eq291 (X0 X1 X3 X4 X5 X6 : G) : (((X4 ◇ ((X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ (((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0)) ◇ X6))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ (X4 ◇ ((X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ (((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0)) ◇ X6)))) = X4 := superpose eq251 eq63
  have eq298 (X0 X1 X2 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = ((((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X4))) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X4)))) := superpose eq251 eq71
  have eq299 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) = ((((X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) ◇ (((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4))) ◇ (X1 ◇ X5))) ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4))))) ◇ ((X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) ◇ (((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4))) ◇ (X1 ◇ X5)))) := superpose eq251 eq72
  have eq429 (X0 X1 X3 X4 X5 : G) : (((X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ (X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0)))) = X4 := superpose eq251 eq291
  have eq430 (X0 X1 X4 X5 : G) : (((X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ X1) ◇ X0))) ◇ X1) ◇ (X4 ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ X1) ◇ X0)))) = X4 := superpose eq251 eq429
  have eq442 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq252 eq298
  have eq451 (X0 X1 X2 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4)))) = (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X4)))) ◇ X0)) := superpose eq252 eq299
  have eq452 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq251 eq451
  have eq453 (X1 X4 X5 : G) : (((X4 ◇ ((X4 ◇ X5) ◇ X1)) ◇ X1) ◇ (X4 ◇ ((X4 ◇ X5) ◇ X1))) = X4 := superpose eq452 eq430
  have eq460 (X1 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ (X4 ◇ X5)) = X4 := superpose eq452 eq453
  have eq515 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) ◇ X2)) = X1 := superpose eq460 eq232
  have eq516 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq452 eq515
  have eq517 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq516 eq442
  have eq532 (X0 X1 : G) : X0 = X1 := superpose eq252 eq517
  have eq536 (X0 : G) : sK0 ≠ X0 := superpose eq532 eq8
  subsumption eq536 eq532


@[equational_result]
theorem Equation31367_implies_Equation2 (G : Type*) [Magma G] (h : Equation31367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) = X3 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X4))) = (((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X4)))))) ◇ (X2 ◇ X0)) ◇ X4) := superpose eq7 eq9
  have eq192 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ ((X4 ◇ X2) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))))))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))))) = (((X5 ◇ ((X5 ◇ X6) ◇ (X6 ◇ ((X4 ◇ ((X4 ◇ X2) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))))))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))))))) ◇ (X6 ◇ (X2 ◇ X1))) ◇ X3) := superpose eq15 eq15
  have eq243 (X1 X2 X3 X5 X6 : G) : (((X5 ◇ ((X5 ◇ X6) ◇ (X6 ◇ X2))) ◇ (X6 ◇ (X2 ◇ X1))) ◇ X3) = X2 := superpose eq7 eq192
  have eq273 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq243 eq11
  have eq330 (X0 X3 : G) : X0 = X3 := superpose eq7 eq273
  have eq524 (X0 : G) : sK0 ≠ X0 := superpose eq330 eq8
  subsumption eq524 eq330


@[equational_result]
theorem Equation31368_implies_Equation2 (G : Type*) [Magma G] (h : Equation31368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31371_implies_Equation2 (G : Type*) [Magma G] (h : Equation31371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation31374_implies_Equation2 (G : Type*) [Magma G] (h : Equation31374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31376_implies_Equation2 (G : Type*) [Magma G] (h : Equation31376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = ((((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0)) ◇ (X3 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0)) ◇ X4))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0))) := superpose eq7 eq9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq7 eq11
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq29 eq7
  have eq79 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq65
  have eq110 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq79 eq79
  have eq114 (X0 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = X2 := superpose eq79 eq10
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq79 eq9
  have eq116 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq79 eq7
  have eq124 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0))) := superpose eq79 eq11
  have eq207 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X1)) ◇ X3))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X1))) := superpose eq116 eq14
  have eq231 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq79 eq114
  have eq235 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq11 eq114
  have eq237 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq114
  have eq238 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq9 eq114
  have eq257 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq116 eq231
  have eq267 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq7 eq235
  have eq363 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X3))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) := superpose eq237 eq207
  have eq380 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq237 eq267
  have eq409 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X3))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) := superpose eq237 eq363
  have eq410 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (X1 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X3))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) := superpose eq114 eq409
  have eq421 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq237 eq238
  have eq422 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) := superpose eq114 eq421
  have eq423 (X0 X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) := superpose eq380 eq422
  have eq546 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq110 eq114
  have eq548 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq237 eq546
  have eq550 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq548 eq257
  have eq592 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq110 eq115
  have eq594 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq116 eq115
  have eq611 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq237 eq592
  have eq612 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq594 eq110
  have eq615 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq594 eq550
  have eq617 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq594 eq611
  have eq618 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq594 eq612
  have eq621 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq594 eq615
  have eq622 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq237 eq617
  have eq623 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq594 eq622
  have eq624 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq618 eq623
  have eq631 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq624 eq124
  have eq655 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) = X1 := superpose eq624 eq423
  have eq696 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq624 eq621
  have eq697 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq624 eq631
  have eq723 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq696 eq410
  have eq734 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq655 eq723
  have eq735 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq697 eq734
  have eq737 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq735 eq114
  have eq867 (X0 X2 : G) : X0 = X2 := superpose eq737 eq737
  have eq869 (X0 : G) : sK0 ≠ X0 := superpose eq867 eq8
  subsumption eq869 eq867


@[equational_result]
theorem Equation31378_implies_Equation2 (G : Type*) [Magma G] (h : Equation31378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31380_implies_Equation2 (G : Type*) [Magma G] (h : Equation31380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X1 := superpose eq14 eq9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq17
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq18 eq10
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq78 eq55


@[equational_result]
theorem Equation31381_implies_Equation2 (G : Type*) [Magma G] (h : Equation31381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) ◇ (X4 ◇ ((X4 ◇ X3) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)))) := superpose eq9 eq10
  have eq43 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X0)) = (X2 ◇ (X4 ◇ ((X4 ◇ X3) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)))) := superpose eq7 eq25
  have eq83 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X4 ◇ ((X4 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := superpose eq10 eq43
  have eq89 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1)))) ◇ X3) := superpose eq43 eq9
  have eq92 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X4 ◇ (((X0 ◇ X3) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) ◇ (X3 ◇ (((X0 ◇ X3) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))))) = X3 := superpose eq43 eq10
  have eq118 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X4 ◇ X5) ◇ (X3 ◇ X5)))) = X3 := superpose eq10 eq83
  have eq123 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ X5)) ◇ (X0 ◇ (X2 ◇ (X6 ◇ ((X6 ◇ X5) ◇ (X0 ◇ X5))))))) = X2 := superpose eq10 eq83
  have eq133 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X2 ◇ X0)) = X2 := superpose eq83 eq83
  have eq198 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ X5)) ◇ (X0 ◇ X0))) = X2 := superpose eq118 eq123
  have eq205 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq133 eq198
  have eq262 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X3) := superpose eq205 eq89
  have eq276 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq205 eq262
  have eq279 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X4 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))))) = X3 := superpose eq276 eq92
  have eq310 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X4) = X3 := superpose eq276 eq279
  have eq311 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq276 eq310
  have eq312 (X0 X3 : G) : X0 = X3 := superpose eq311 eq311
  have eq317 (X0 : G) : sK0 ≠ X0 := superpose eq312 eq8
  subsumption eq317 eq312


@[equational_result]
theorem Equation31382_implies_Equation2 (G : Type*) [Magma G] (h : Equation31382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X4 ◇ X3))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31384_implies_Equation2 (G : Type*) [Magma G] (h : Equation31384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := superpose eq10 eq14
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq23 eq12
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq31 eq31
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq14 eq31
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq41 eq44
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq82 eq72


@[equational_result]
theorem Equation31386_implies_Equation2 (G : Type*) [Magma G] (h : Equation31386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31390_implies_Equation2 (G : Type*) [Magma G] (h : Equation31390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X4 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31392_implies_Equation2 (G : Type*) [Magma G] (h : Equation31392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X5))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) = (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq31 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) ◇ (X5 ◇ X6)) = X0 := superpose eq7 eq11
  have eq48 (X0 X1 X2 X5 X6 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X5 ◇ X6)) = X0 := superpose eq14 eq31
  have eq62 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X4) = X0 := superpose eq7 eq15
  have eq87 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) = X1 := superpose eq62 eq9
  have eq94 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X5)))) := superpose eq7 eq87
  have eq133 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq62 eq94
  have eq134 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq133 eq87
  have eq135 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X0 := superpose eq133 eq62
  have eq139 (X0 X2 X5 X6 : G) : (X2 ◇ (X5 ◇ X6)) = X0 := superpose eq135 eq48
  have eq155 (X0 X2 : G) : X0 = X2 := superpose eq134 eq139
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq162 eq155


@[equational_result]
theorem Equation31393_implies_Equation2 (G : Type*) [Magma G] (h : Equation31393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = (X0 ◇ X4) := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq12 eq7
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation31394_implies_Equation2 (G : Type*) [Magma G] (h : Equation31394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X5))) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation31395_implies_Equation2 (G : Type*) [Magma G] (h : Equation31395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X5 ◇ X6))) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31398_implies_Equation2 (G : Type*) [Magma G] (h : Equation31398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation31401_implies_Equation2 (G : Type*) [Magma G] (h : Equation31401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation31403_implies_Equation2 (G : Type*) [Magma G] (h : Equation31403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) = ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))) ◇ X2) = X3 := superpose eq9 eq7
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq17 eq20
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq58 eq27


@[equational_result]
theorem Equation31405_implies_Equation2 (G : Type*) [Magma G] (h : Equation31405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation31408_implies_Equation2 (G : Type*) [Magma G] (h : Equation31408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X2))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation31410_implies_Equation2 (G : Type*) [Magma G] (h : Equation31410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation31411_implies_Equation2 (G : Type*) [Magma G] (h : Equation31411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31413_implies_Equation2 (G : Type*) [Magma G] (h : Equation31413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31414_implies_Equation2 (G : Type*) [Magma G] (h : Equation31414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31415_implies_Equation2 (G : Type*) [Magma G] (h : Equation31415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31417_implies_Equation2 (G : Type*) [Magma G] (h : Equation31417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq23 eq13


@[equational_result]
theorem Equation31419_implies_Equation2 (G : Type*) [Magma G] (h : Equation31419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation31421_implies_Equation2 (G : Type*) [Magma G] (h : Equation31421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31422_implies_Equation2 (G : Type*) [Magma G] (h : Equation31422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31423_implies_Equation2 (G : Type*) [Magma G] (h : Equation31423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31425_implies_Equation2 (G : Type*) [Magma G] (h : Equation31425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31426_implies_Equation2 (G : Type*) [Magma G] (h : Equation31426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31427_implies_Equation2 (G : Type*) [Magma G] (h : Equation31427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31429_implies_Equation2 (G : Type*) [Magma G] (h : Equation31429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31430_implies_Equation2 (G : Type*) [Magma G] (h : Equation31430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31431_implies_Equation2 (G : Type*) [Magma G] (h : Equation31431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31432_implies_Equation2 (G : Type*) [Magma G] (h : Equation31432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31434_implies_Equation2 (G : Type*) [Magma G] (h : Equation31434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq27 eq12


@[equational_result]
theorem Equation31435_implies_Equation2 (G : Type*) [Magma G] (h : Equation31435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X3))) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq10 eq10
  have eq23 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq9
  have eq28 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X2))) = X2 := superpose eq7 eq9
  have eq35 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq28 eq16
  have eq37 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X1 := superpose eq35 eq23
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := superpose eq35 eq7
  have eq53 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq35 eq28
  have eq56 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq35 eq37
  have eq57 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq35 eq56
  have eq58 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq35 eq57
  have eq90 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq53 eq58
  have eq91 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq90 eq43
  have eq107 (X0 X3 : G) : X0 = X3 := superpose eq91 eq91
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq109 eq107


@[equational_result]
theorem Equation31436_implies_Equation2 (G : Type*) [Magma G] (h : Equation31436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X4 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31438_implies_Equation2 (G : Type*) [Magma G] (h : Equation31438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ X0))) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq7 eq10
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X0) = X2 := superpose eq25 eq24
  have eq84 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq7 eq33
  have eq141 (X0 X1 : G) : X0 = X1 := superpose eq33 eq84
  have eq268 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq268 eq141


@[equational_result]
theorem Equation31440_implies_Equation2 (G : Type*) [Magma G] (h : Equation31440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31444_implies_Equation2 (G : Type*) [Magma G] (h : Equation31444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X4 ◇ X3))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31446_implies_Equation2 (G : Type*) [Magma G] (h : Equation31446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq38 eq16


@[equational_result]
theorem Equation31447_implies_Equation2 (G : Type*) [Magma G] (h : Equation31447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X5))) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X3 := superpose eq11 eq11
  have eq40 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq9
  have eq50 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq40 eq21
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq50 eq50
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq159 eq52


@[equational_result]
theorem Equation31448_implies_Equation2 (G : Type*) [Magma G] (h : Equation31448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation31449_implies_Equation2 (G : Type*) [Magma G] (h : Equation31449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X5 ◇ X6))) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31451_implies_Equation2 (G : Type*) [Magma G] (h : Equation31451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = ((((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ (X3 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X0))) ◇ ((((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ (X3 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X0))) ◇ X4) ◇ X0)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ (X3 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X0)))) := superpose eq9 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = ((((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X0)) ◇ ((((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X0)) ◇ X4) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X0))) := superpose eq7 eq10
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq7 eq11
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq29 eq7
  have eq79 (X0 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq66
  have eq111 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq79 eq79
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) := superpose eq79 eq10
  have eq116 (X0 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = X2 := superpose eq79 eq9
  have eq117 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq79 eq7
  have eq121 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq79 eq7
  have eq151 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) ◇ (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) := superpose eq79 eq16
  have eq188 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = ((((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) ◇ X2)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) ◇ X2))) := superpose eq117 eq22
  have eq237 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq117 eq116
  have eq254 (X0 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) = X0 := superpose eq237 eq79
  have eq255 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq237 eq111
  have eq258 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X2) ◇ X0) := superpose eq237 eq121
  have eq265 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) ◇ (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) := superpose eq237 eq151
  have eq275 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X2) ◇ X0) := superpose eq254 eq258
  have eq276 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq117 eq275
  have eq296 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq276 eq265
  have eq297 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq255 eq296
  have eq298 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) := superpose eq276 eq297
  have eq299 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq115 eq298
  have eq300 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq237 eq299
  have eq446 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq300 eq7
  have eq483 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq446 eq188
  have eq527 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq483 eq7
  have eq874 (X0 X2 : G) : X0 = X2 := superpose eq527 eq527
  have eq879 (X0 : G) : sK0 ≠ X0 := superpose eq874 eq8
  subsumption eq879 eq874


@[equational_result]
theorem Equation31453_implies_Equation2 (G : Type*) [Magma G] (h : Equation31453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31455_implies_Equation2 (G : Type*) [Magma G] (h : Equation31455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31456_implies_Equation2 (G : Type*) [Magma G] (h : Equation31456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31457_implies_Equation2 (G : Type*) [Magma G] (h : Equation31457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31459_implies_Equation2 (G : Type*) [Magma G] (h : Equation31459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31460_implies_Equation2 (G : Type*) [Magma G] (h : Equation31460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31461_implies_Equation2 (G : Type*) [Magma G] (h : Equation31461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31463_implies_Equation2 (G : Type*) [Magma G] (h : Equation31463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31464_implies_Equation2 (G : Type*) [Magma G] (h : Equation31464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31465_implies_Equation2 (G : Type*) [Magma G] (h : Equation31465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31466_implies_Equation2 (G : Type*) [Magma G] (h : Equation31466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31470_implies_Equation2 (G : Type*) [Magma G] (h : Equation31470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31472_implies_Equation2 (G : Type*) [Magma G] (h : Equation31472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31473_implies_Equation2 (G : Type*) [Magma G] (h : Equation31473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31474_implies_Equation2 (G : Type*) [Magma G] (h : Equation31474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31476_implies_Equation2 (G : Type*) [Magma G] (h : Equation31476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31477_implies_Equation2 (G : Type*) [Magma G] (h : Equation31477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31478_implies_Equation2 (G : Type*) [Magma G] (h : Equation31478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31480_implies_Equation2 (G : Type*) [Magma G] (h : Equation31480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31481_implies_Equation2 (G : Type*) [Magma G] (h : Equation31481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31482_implies_Equation2 (G : Type*) [Magma G] (h : Equation31482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31483_implies_Equation2 (G : Type*) [Magma G] (h : Equation31483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31485_implies_Equation2 (G : Type*) [Magma G] (h : Equation31485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation31486_implies_Equation2 (G : Type*) [Magma G] (h : Equation31486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation31487_implies_Equation2 (G : Type*) [Magma G] (h : Equation31487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X3) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation31488_implies_Equation2 (G : Type*) [Magma G] (h : Equation31488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ (X0 ◇ (X5 ◇ X6))) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation31490_implies_Equation2 (G : Type*) [Magma G] (h : Equation31490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31491_implies_Equation2 (G : Type*) [Magma G] (h : Equation31491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31492_implies_Equation2 (G : Type*) [Magma G] (h : Equation31492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31493_implies_Equation2 (G : Type*) [Magma G] (h : Equation31493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31495_implies_Equation2 (G : Type*) [Magma G] (h : Equation31495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31496_implies_Equation2 (G : Type*) [Magma G] (h : Equation31496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


