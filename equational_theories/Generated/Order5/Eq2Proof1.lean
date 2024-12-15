import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation4900_implies_Equation2 (G : Type*) [Magma G] (h : Equation4900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq9 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq13 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq14
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation4903_implies_Equation2 (G : Type*) [Magma G] (h : Equation4903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq15
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq16
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq17 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq17 eq19
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq21 eq17
  have eq23 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq22 eq21
  have eq26 (X0 X1 : G) : X0 = X1 := superpose eq23 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation4905_implies_Equation2 (G : Type*) [Magma G] (h : Equation4905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq12 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq14 eq11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq12 eq16
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq12 eq18
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)))) := superpose eq17 eq7
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)))) := superpose eq19 eq25
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq19 eq26
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq19 eq31
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq32 eq27
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq33 eq32
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq34 eq19
  have eq37 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq35 eq15
  have eq44 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq35 eq37
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq44 eq34
  have eq46 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq12
  have eq52 (X0 X1 : G) : X0 = X1 := superpose eq46 eq45
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq54 eq52


@[equational_result]
theorem Equation4906_implies_Equation2 (G : Type*) [Magma G] (h : Equation4906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq10 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq10 eq11
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation4907_implies_Equation2 (G : Type*) [Magma G] (h : Equation4907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation4910_implies_Equation2 (G : Type*) [Magma G] (h : Equation4910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := superpose eq13 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq13 eq14
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq17
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation4913_implies_Equation2 (G : Type*) [Magma G] (h : Equation4913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq10 eq17
  have eq43 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq36 eq9
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq43
  have eq55 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq45 eq36
  have eq60 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq55 eq17
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq60 eq60
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq79 eq71


@[equational_result]
theorem Equation4915_implies_Equation2 (G : Type*) [Magma G] (h : Equation4915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) = X3 := superpose eq10 eq9
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq14
  have eq56 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq13 eq14
  have eq61 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1)))) = X3 := superpose eq7 eq19
  have eq67 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq19
  have eq72 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq19
  have eq82 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq72
  have eq103 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq14 eq82
  have eq111 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq82 eq7
  have eq125 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq82 eq103
  have eq127 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq125 eq67
  have eq140 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq111 eq56
  have eq141 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq140 eq36
  have eq218 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq141 eq141
  have eq220 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq141 eq127
  have eq226 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq125 eq220
  have eq227 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq226 eq218
  have eq228 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) = X3 := superpose eq227 eq61
  have eq234 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X3 := superpose eq227 eq228
  have eq235 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq227 eq234
  have eq236 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq227 eq235
  have eq237 (X0 X1 : G) : X0 = X1 := superpose eq125 eq236
  have eq245 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq245 eq237


@[equational_result]
theorem Equation4917_implies_Equation2 (G : Type*) [Magma G] (h : Equation4917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq15
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := superpose eq16 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq17 eq17
  have eq25 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq21 eq10
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq25 eq21
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq12 eq29
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq39 eq31


@[equational_result]
theorem Equation4919_implies_Equation2 (G : Type*) [Magma G] (h : Equation4919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq7
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := superpose eq15 eq10
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X1 := superpose eq7 eq21
  have eq101 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq37
  have eq123 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq101 eq14
  have eq169 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq101 eq123
  have eq170 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq101 eq169
  have eq245 (X0 X2 : G) : X0 = X2 := superpose eq170 eq170
  have eq253 (X0 : G) : sK0 ≠ X0 := superpose eq245 eq8
  subsumption eq253 eq245


@[equational_result]
theorem Equation4920_implies_Equation2 (G : Type*) [Magma G] (h : Equation4920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))))) = X2 := superpose eq11 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq38 eq18


@[equational_result]
theorem Equation4921_implies_Equation2 (G : Type*) [Magma G] (h : Equation4921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := superpose eq13 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq13 eq14
  have eq18 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq13 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation4923_implies_Equation2 (G : Type*) [Magma G] (h : Equation4923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq10 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq10 eq12
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := superpose eq18 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq18 eq9
  have eq24 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq18 eq11
  have eq25 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq18 eq13
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq18 eq25
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq28 eq22
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq21 eq21
  have eq43 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq35 eq21
  have eq44 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq35 eq43
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq28 eq44
  have eq47 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq45 eq24
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq47 eq28
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq53 eq29
  have eq62 (X0 X2 : G) : X0 = X2 := superpose eq54 eq54
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq70 eq62


@[equational_result]
theorem Equation4924_implies_Equation2 (G : Type*) [Magma G] (h : Equation4924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose eq10 eq10
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) = X0 := superpose eq9 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq13 eq7
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) = (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)) := superpose eq13 eq9
  have eq36 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq31 eq24
  have eq40 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq31 eq12
  have eq41 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq31 eq10
  have eq42 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq31 eq36
  have eq46 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq42 eq40
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq42 eq46
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq41
  have eq67 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq55 eq47
  have eq79 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq67 eq32
  have eq97 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq67 eq67
  have eq101 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X2)) := superpose eq97 eq79
  have eq108 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq67 eq101
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq108 eq14
  have eq119 (X0 X1 : G) : X0 = X1 := superpose eq109 eq108
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq121 eq119


@[equational_result]
theorem Equation4925_implies_Equation2 (G : Type*) [Magma G] (h : Equation4925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq10
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq12 eq13
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq12 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation4927_implies_Equation2 (G : Type*) [Magma G] (h : Equation4927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq12 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq15 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq16 eq7
  have eq19 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq18 eq16
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq19 eq18
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation4928_implies_Equation2 (G : Type*) [Magma G] (h : Equation4928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq12 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq12 eq13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation4929_implies_Equation2 (G : Type*) [Magma G] (h : Equation4929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq14 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation4931_implies_Equation2 (G : Type*) [Magma G] (h : Equation4931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq23 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) = X4 := superpose eq23 eq10
  have eq43 (X1 X4 : G) : (X1 ◇ X4) = X4 := superpose eq23 eq34
  have eq47 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq43 eq23
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq63 eq50


@[equational_result]
theorem Equation4932_implies_Equation2 (G : Type*) [Magma G] (h : Equation4932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq14 eq11
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X0)) = X3 := superpose eq14 eq15
  have eq18 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq17
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation4933_implies_Equation2 (G : Type*) [Magma G] (h : Equation4933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq12 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation4934_implies_Equation2 (G : Type*) [Magma G] (h : Equation4934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation4937_implies_Equation2 (G : Type*) [Magma G] (h : Equation4937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq7
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq25 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq21
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq61 eq48


@[equational_result]
theorem Equation4940_implies_Equation2 (G : Type*) [Magma G] (h : Equation4940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation4942_implies_Equation2 (G : Type*) [Magma G] (h : Equation4942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = (X0 ◇ X0) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq13 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) = X1 := superpose eq17 eq18
  have eq23 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq13
  have eq33 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq23 eq19
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq17 eq33
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq50 eq44


@[equational_result]
theorem Equation4943_implies_Equation2 (G : Type*) [Magma G] (h : Equation4943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq39 eq13


@[equational_result]
theorem Equation4944_implies_Equation2 (G : Type*) [Magma G] (h : Equation4944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation4947_implies_Equation2 (G : Type*) [Magma G] (h : Equation4947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq7
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq9
  have eq42 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq29 eq10
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq42 eq42
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq57 eq52


@[equational_result]
theorem Equation4950_implies_Equation2 (G : Type*) [Magma G] (h : Equation4950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq9
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq29
  have eq37 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq35 eq9
  have eq41 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq35 eq37
  have eq45 (X0 X1 : G) : X0 = X1 := superpose eq41 eq35
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq47 eq45


@[equational_result]
theorem Equation4953_implies_Equation2 (G : Type*) [Magma G] (h : Equation4953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) = X2 := superpose eq7 eq9
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq9
  have eq23 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq16
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := superpose eq20 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq28 eq28
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq23 eq30
  have eq47 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq41 eq30
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq47 eq47
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq59 eq54


@[equational_result]
theorem Equation4954_implies_Equation2 (G : Type*) [Magma G] (h : Equation4954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq10 eq15
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq10
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq23 eq16
  have eq35 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq33 eq23
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq33 eq35
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation4956_implies_Equation2 (G : Type*) [Magma G] (h : Equation4956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq9 eq7
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq27 eq7
  have eq62 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq34 eq7
  have eq70 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq34 eq62
  have eq71 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq70 eq27
  have eq103 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq71 eq7
  have eq113 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq103 eq71
  have eq146 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq113 eq7
  have eq157 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq113 eq146
  have eq186 (X0 X1 : G) : X0 = X1 := superpose eq157 eq113
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq186 eq8
  subsumption eq188 eq186


@[equational_result]
theorem Equation4958_implies_Equation2 (G : Type*) [Magma G] (h : Equation4958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq32 eq13


@[equational_result]
theorem Equation4960_implies_Equation2 (G : Type*) [Magma G] (h : Equation4960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq10 eq17
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq31 eq19


@[equational_result]
theorem Equation4962_implies_Equation2 (G : Type*) [Magma G] (h : Equation4962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq11 eq9
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation4965_implies_Equation2 (G : Type*) [Magma G] (h : Equation4965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose eq9 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq9 eq11
  have eq17 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq13 eq13
  have eq25 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq9
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq17 eq7
  have eq48 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq39 eq14
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq48 eq7
  have eq50 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq48 eq9
  have eq55 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose eq48 eq25
  have eq63 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq50 eq55
  have eq64 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq63 eq49
  have eq86 (X0 X1 : G) : X0 = X1 := superpose eq64 eq63
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq110 eq86


@[equational_result]
theorem Equation4966_implies_Equation2 (G : Type*) [Magma G] (h : Equation4966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq32 eq13


@[equational_result]
theorem Equation4968_implies_Equation2 (G : Type*) [Magma G] (h : Equation4968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq13
  have eq52 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq33 eq7
  have eq70 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq33 eq52
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq11 eq70
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq84 eq73


@[equational_result]
theorem Equation4969_implies_Equation2 (G : Type*) [Magma G] (h : Equation4969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation4970_implies_Equation2 (G : Type*) [Magma G] (h : Equation4970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation4971_implies_Equation2 (G : Type*) [Magma G] (h : Equation4971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation4973_implies_Equation2 (G : Type*) [Magma G] (h : Equation4973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq11
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq19 eq10
  have eq36 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq19 eq21
  have eq46 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq19 eq36
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq46
  have eq62 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq58 eq16
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq62
  have eq166 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := superpose eq152 eq7
  have eq193 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq152 eq166
  have eq194 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq152 eq193
  have eq195 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq152 eq194
  have eq283 (X0 X2 : G) : X0 = X2 := superpose eq195 eq195
  have eq288 (X0 : G) : sK0 ≠ X0 := superpose eq283 eq8
  subsumption eq288 eq283


@[equational_result]
theorem Equation4974_implies_Equation2 (G : Type*) [Magma G] (h : Equation4974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq11
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq16
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X0)))) = X2 := superpose eq17 eq9
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X0))) = X2 := superpose eq17 eq18
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq17 eq23
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq24
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq31 eq26


@[equational_result]
theorem Equation4975_implies_Equation2 (G : Type*) [Magma G] (h : Equation4975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq12 eq14
  have eq19 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq18
  have eq20 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq19
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation4977_implies_Equation2 (G : Type*) [Magma G] (h : Equation4977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq10 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq10 eq9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0))) := superpose eq9 eq7
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq14
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq22 eq19
  have eq38 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq22 eq17
  have eq52 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq38 eq22
  have eq61 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq52 eq34
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq10 eq61
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq85 eq62


@[equational_result]
theorem Equation4978_implies_Equation2 (G : Type*) [Magma G] (h : Equation4978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq21 eq20
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq10 eq24
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq24 eq24
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) := superpose eq7 eq24
  have eq38 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) = X3 := superpose eq24 eq7
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0)))) = X2 := superpose eq24 eq7
  have eq49 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq24 eq10
  have eq56 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq32 eq29
  have eq62 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = X3 := superpose eq31 eq38
  have eq64 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq49 eq48
  have eq66 (X0 X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ (X3 ◇ X0)) := superpose eq64 eq56
  have eq79 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq66 eq62
  have eq87 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq64 eq79
  have eq99 (X0 X1 : G) : X0 = X1 := superpose eq11 eq87
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq143 eq99


@[equational_result]
theorem Equation4979_implies_Equation2 (G : Type*) [Magma G] (h : Equation4979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq33 eq13


@[equational_result]
theorem Equation4981_implies_Equation2 (G : Type*) [Magma G] (h : Equation4981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq31 eq14


@[equational_result]
theorem Equation4982_implies_Equation2 (G : Type*) [Magma G] (h : Equation4982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation4983_implies_Equation2 (G : Type*) [Magma G] (h : Equation4983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation4985_implies_Equation2 (G : Type*) [Magma G] (h : Equation4985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq35 eq15


@[equational_result]
theorem Equation4986_implies_Equation2 (G : Type*) [Magma G] (h : Equation4986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X3)))) ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ X0)))) = X2 := superpose eq12 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq13
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq12 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq28 eq24


@[equational_result]
theorem Equation4987_implies_Equation2 (G : Type*) [Magma G] (h : Equation4987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq10 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq25 eq14


@[equational_result]
theorem Equation4988_implies_Equation2 (G : Type*) [Magma G] (h : Equation4988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation4990_implies_Equation2 (G : Type*) [Magma G] (h : Equation4990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))))) = X2 := superpose eq10 eq9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))))) = X2 := superpose eq12 eq11
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X2 := superpose eq17 eq16
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq15 eq18
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq17 eq21
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq30 eq26


@[equational_result]
theorem Equation4991_implies_Equation2 (G : Type*) [Magma G] (h : Equation4991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq9 eq7
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq108 eq48


@[equational_result]
theorem Equation4992_implies_Equation2 (G : Type*) [Magma G] (h : Equation4992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation4994_implies_Equation2 (G : Type*) [Magma G] (h : Equation4994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := superpose eq9 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq13 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq24 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq29
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation4995_implies_Equation2 (G : Type*) [Magma G] (h : Equation4995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq11 eq7
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq12
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq12
  have eq34 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := superpose eq12 eq10
  have eq38 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq28 eq13
  have eq50 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq29 eq34
  have eq61 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ X4)))) ◇ X0))) = X2 := superpose eq7 eq9
  have eq64 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := superpose eq7 eq9
  have eq77 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq29 eq7
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq50 eq77
  have eq107 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X1 ◇ X4)))) ◇ X0))) = X2 := superpose eq87 eq61
  have eq110 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq87 eq64
  have eq130 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X2 := superpose eq87 eq107
  have eq149 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq38 eq110
  have eq156 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq149 eq87
  have eq157 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X2 := superpose eq156 eq130
  have eq173 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq156 eq157
  have eq174 (X0 X1 : G) : X0 = X1 := superpose eq29 eq173
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq174 eq8
  subsumption eq179 eq174


@[equational_result]
theorem Equation4996_implies_Equation2 (G : Type*) [Magma G] (h : Equation4996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq13
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq17 eq12
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation4998_implies_Equation2 (G : Type*) [Magma G] (h : Equation4998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq12 eq10
  have eq22 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq15 eq12
  have eq24 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq15
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq24 eq22
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq29 eq15
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq31 eq7
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq38
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq40 eq40
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq40 eq42
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq58 eq43


@[equational_result]
theorem Equation5000_implies_Equation2 (G : Type*) [Magma G] (h : Equation5000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq12 eq10
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq13
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation5002_implies_Equation2 (G : Type*) [Magma G] (h : Equation5002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation5003_implies_Equation2 (G : Type*) [Magma G] (h : Equation5003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation5004_implies_Equation2 (G : Type*) [Magma G] (h : Equation5004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq62 eq48


@[equational_result]
theorem Equation5005_implies_Equation2 (G : Type*) [Magma G] (h : Equation5005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5007_implies_Equation2 (G : Type*) [Magma G] (h : Equation5007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq12 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) = X0 := superpose eq12 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq12 eq14
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq15 eq7
  have eq30 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq7
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq15 eq10
  have eq36 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq10
  have eq55 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq29 eq36
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) = X2 := superpose eq55 eq35
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X2 := superpose eq30 eq56
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq57 eq55
  have eq62 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq58 eq13
  have eq71 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq62
  have eq73 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = X0 := superpose eq71 eq10
  have eq84 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq71 eq73
  have eq112 (X0 X1 : G) : X0 = X1 := superpose eq84 eq71
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq125 eq112


@[equational_result]
theorem Equation5008_implies_Equation2 (G : Type*) [Magma G] (h : Equation5008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0))) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))))) = X2 := superpose eq16 eq9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq51 eq25


@[equational_result]
theorem Equation5009_implies_Equation2 (G : Type*) [Magma G] (h : Equation5009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation5013_implies_Equation2 (G : Type*) [Magma G] (h : Equation5013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5016_implies_Equation2 (G : Type*) [Magma G] (h : Equation5016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation5017_implies_Equation2 (G : Type*) [Magma G] (h : Equation5017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5019_implies_Equation2 (G : Type*) [Magma G] (h : Equation5019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation5020_implies_Equation2 (G : Type*) [Magma G] (h : Equation5020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5021_implies_Equation2 (G : Type*) [Magma G] (h : Equation5021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X3 := superpose eq7 eq7
  have eq12 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation5022_implies_Equation2 (G : Type*) [Magma G] (h : Equation5022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5024_implies_Equation2 (G : Type*) [Magma G] (h : Equation5024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq12 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = X0 := superpose eq19 eq10
  have eq21 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq16 eq20
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq12 eq21
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq60 eq26


@[equational_result]
theorem Equation5025_implies_Equation2 (G : Type*) [Magma G] (h : Equation5025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5026_implies_Equation2 (G : Type*) [Magma G] (h : Equation5026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X5)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X5) ◇ X0)))) = X2 := superpose eq10 eq9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq7
  have eq14 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq13 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation5027_implies_Equation2 (G : Type*) [Magma G] (h : Equation5027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5029_implies_Equation2 (G : Type*) [Magma G] (h : Equation5029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq34 eq13


@[equational_result]
theorem Equation5030_implies_Equation2 (G : Type*) [Magma G] (h : Equation5030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5031_implies_Equation2 (G : Type*) [Magma G] (h : Equation5031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5032_implies_Equation2 (G : Type*) [Magma G] (h : Equation5032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5034_implies_Equation2 (G : Type*) [Magma G] (h : Equation5034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation5035_implies_Equation2 (G : Type*) [Magma G] (h : Equation5035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq57 eq17


@[equational_result]
theorem Equation5036_implies_Equation2 (G : Type*) [Magma G] (h : Equation5036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5037_implies_Equation2 (G : Type*) [Magma G] (h : Equation5037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5039_implies_Equation2 (G : Type*) [Magma G] (h : Equation5039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation5040_implies_Equation2 (G : Type*) [Magma G] (h : Equation5040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5041_implies_Equation2 (G : Type*) [Magma G] (h : Equation5041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X3 := superpose eq7 eq7
  have eq12 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation5042_implies_Equation2 (G : Type*) [Magma G] (h : Equation5042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5044_implies_Equation2 (G : Type*) [Magma G] (h : Equation5044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation5045_implies_Equation2 (G : Type*) [Magma G] (h : Equation5045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5046_implies_Equation2 (G : Type*) [Magma G] (h : Equation5046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5047_implies_Equation2 (G : Type*) [Magma G] (h : Equation5047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5048_implies_Equation2 (G : Type*) [Magma G] (h : Equation5048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5051_implies_Equation2 (G : Type*) [Magma G] (h : Equation5051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq13 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq45 eq20


@[equational_result]
theorem Equation5054_implies_Equation2 (G : Type*) [Magma G] (h : Equation5054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq12 eq11
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation5056_implies_Equation2 (G : Type*) [Magma G] (h : Equation5056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq11 eq7
  have eq20 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) = X2 := superpose eq14 eq10
  have eq22 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq14 eq7
  have eq23 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0))) = X2 := superpose eq17 eq20
  have eq24 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq17 eq23
  have eq43 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X2 ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq15 eq11
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq22 eq24
  have eq71 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq11 eq47
  have eq72 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq17 eq71
  have eq75 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq72 eq22
  have eq77 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq75 eq72
  have eq80 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X0)) = X1 := superpose eq77 eq17
  have eq90 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X2))) = X0 := superpose eq80 eq43
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq90 eq15
  have eq94 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq93 eq11
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq93 eq94
  have eq100 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq93 eq99
  have eq103 (X0 X1 : G) : X0 = X1 := superpose eq100 eq93
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq105 eq103


@[equational_result]
theorem Equation5057_implies_Equation2 (G : Type*) [Magma G] (h : Equation5057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq10 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq10 eq12
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := superpose eq14 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq29 eq23


@[equational_result]
theorem Equation5058_implies_Equation2 (G : Type*) [Magma G] (h : Equation5058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq20 eq17


@[equational_result]
theorem Equation5061_implies_Equation2 (G : Type*) [Magma G] (h : Equation5061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq27 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq19 eq9
  have eq31 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq19 eq27
  have eq34 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq39 eq34


@[equational_result]
theorem Equation5064_implies_Equation2 (G : Type*) [Magma G] (h : Equation5064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq10 eq10
  have eq22 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq20 eq10
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq33 eq28


@[equational_result]
theorem Equation5067_implies_Equation2 (G : Type*) [Magma G] (h : Equation5067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq9
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq15 eq7
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq18
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq16 eq23
  have eq25 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq24 eq18
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq33 eq28


@[equational_result]
theorem Equation5068_implies_Equation2 (G : Type*) [Magma G] (h : Equation5068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq15
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq16 eq7
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation5070_implies_Equation2 (G : Type*) [Magma G] (h : Equation5070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq11 eq7
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1))) ◇ (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1))) ◇ X0)) = X1 := superpose eq7 eq10
  have eq24 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq24 eq12
  have eq33 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq24 eq11
  have eq36 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq24 eq7
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq33 eq33
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq32 eq41
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq48 eq32
  have eq55 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq50 eq36
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq55 eq50
  have eq58 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq24 eq56
  have eq59 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1)) ◇ (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1)) ◇ X0)) = X1 := superpose eq58 eq21
  have eq76 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1)) ◇ X0) = X1 := superpose eq58 eq59
  have eq77 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1) ◇ X0) = X1 := superpose eq58 eq76
  have eq78 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq58 eq77
  have eq144 (X0 X1 : G) : X0 = X1 := superpose eq58 eq78
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq146 eq144


@[equational_result]
theorem Equation5072_implies_Equation2 (G : Type*) [Magma G] (h : Equation5072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5074_implies_Equation2 (G : Type*) [Magma G] (h : Equation5074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0))) = X2 := superpose eq9 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := superpose eq9 eq10
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq47 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq16 eq7
  have eq66 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X2 ◇ X2)) := superpose eq15 eq47
  have eq70 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq66 eq12
  have eq71 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq66 eq15
  have eq84 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq66 eq71
  have eq85 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq84 eq66
  have eq86 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq85 eq84
  have eq87 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq85 eq70
  have eq89 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq86 eq87
  have eq90 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq86 eq89
  have eq134 (X0 X2 : G) : X0 = X2 := superpose eq90 eq90
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq134 eq8
  subsumption eq136 eq134


@[equational_result]
theorem Equation5075_implies_Equation2 (G : Type*) [Magma G] (h : Equation5075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq11
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq7
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq25 eq27
  have eq105 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq113 eq105


@[equational_result]
theorem Equation5076_implies_Equation2 (G : Type*) [Magma G] (h : Equation5076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5078_implies_Equation2 (G : Type*) [Magma G] (h : Equation5078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ (X3 ◇ X4))) ◇ (((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0)) = X1 := superpose eq7 eq10
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq11
  have eq114 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq31
  have eq121 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) = (X1 ◇ X0) := superpose eq7 eq31
  have eq156 (X0 X1 X3 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X4))) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0)) = X1 := superpose eq114 eq26
  have eq185 (X0 X1 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X4) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X4) ◇ X0)) = X1 := superpose eq114 eq156
  have eq194 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq114 eq121
  have eq202 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ (((X1 ◇ X0) ◇ X4) ◇ X0)) = X1 := superpose eq194 eq185
  have eq275 (X0 X1 : G) : X0 = X1 := superpose eq114 eq202
  have eq279 (X0 : G) : sK0 ≠ X0 := superpose eq275 eq8
  subsumption eq279 eq275


@[equational_result]
theorem Equation5079_implies_Equation2 (G : Type*) [Magma G] (h : Equation5079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9
  have eq20 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq16 eq9
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation5080_implies_Equation2 (G : Type*) [Magma G] (h : Equation5080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq12 eq9
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5082_implies_Equation2 (G : Type*) [Magma G] (h : Equation5082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation5083_implies_Equation2 (G : Type*) [Magma G] (h : Equation5083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X4)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X0)))) = X2 := superpose eq12 eq9
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq12 eq13
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation5084_implies_Equation2 (G : Type*) [Magma G] (h : Equation5084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5085_implies_Equation2 (G : Type*) [Magma G] (h : Equation5085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5088_implies_Equation2 (G : Type*) [Magma G] (h : Equation5088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5091_implies_Equation2 (G : Type*) [Magma G] (h : Equation5091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5094_implies_Equation2 (G : Type*) [Magma G] (h : Equation5094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq10 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq12
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq15 eq10
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq17 eq12
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation5095_implies_Equation2 (G : Type*) [Magma G] (h : Equation5095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq11 eq9
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq12 eq13
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5098_implies_Equation2 (G : Type*) [Magma G] (h : Equation5098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5100_implies_Equation2 (G : Type*) [Magma G] (h : Equation5100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5101_implies_Equation2 (G : Type*) [Magma G] (h : Equation5101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5103_implies_Equation2 (G : Type*) [Magma G] (h : Equation5103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5104_implies_Equation2 (G : Type*) [Magma G] (h : Equation5104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5105_implies_Equation2 (G : Type*) [Magma G] (h : Equation5105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5109_implies_Equation2 (G : Type*) [Magma G] (h : Equation5109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation5111_implies_Equation2 (G : Type*) [Magma G] (h : Equation5111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5112_implies_Equation2 (G : Type*) [Magma G] (h : Equation5112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5113_implies_Equation2 (G : Type*) [Magma G] (h : Equation5113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5115_implies_Equation2 (G : Type*) [Magma G] (h : Equation5115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5116_implies_Equation2 (G : Type*) [Magma G] (h : Equation5116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5117_implies_Equation2 (G : Type*) [Magma G] (h : Equation5117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5119_implies_Equation2 (G : Type*) [Magma G] (h : Equation5119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5120_implies_Equation2 (G : Type*) [Magma G] (h : Equation5120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5121_implies_Equation2 (G : Type*) [Magma G] (h : Equation5121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5122_implies_Equation2 (G : Type*) [Magma G] (h : Equation5122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5124_implies_Equation2 (G : Type*) [Magma G] (h : Equation5124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq11 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq12
  have eq19 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0))) = X2 := superpose eq14 eq10
  have eq21 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq14 eq7
  have eq22 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq14 eq13
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq18
  have eq25 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq14 eq21
  have eq26 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq14 eq22
  have eq27 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq26 eq11
  have eq30 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq25 eq25
  have eq37 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) = X1 := superpose eq25 eq30
  have eq39 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq30 eq30
  have eq44 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq16 eq39
  have eq45 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq16 eq44
  have eq46 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq23 eq45
  have eq47 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose eq46 eq37
  have eq51 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq27 eq47
  have eq54 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X2 := superpose eq51 eq19
  have eq63 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq51 eq54
  have eq69 (X0 X2 : G) : X0 = X2 := superpose eq63 eq63
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq71 eq69


@[equational_result]
theorem Equation5125_implies_Equation2 (G : Type*) [Magma G] (h : Equation5125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq40 eq28


@[equational_result]
theorem Equation5126_implies_Equation2 (G : Type*) [Magma G] (h : Equation5126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation5128_implies_Equation2 (G : Type*) [Magma G] (h : Equation5128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq9 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) = X1 := superpose eq10 eq7
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq17
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq68 eq26


@[equational_result]
theorem Equation5130_implies_Equation2 (G : Type*) [Magma G] (h : Equation5130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq43 eq13


@[equational_result]
theorem Equation5134_implies_Equation2 (G : Type*) [Magma G] (h : Equation5134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq43 eq13


@[equational_result]
theorem Equation5136_implies_Equation2 (G : Type*) [Magma G] (h : Equation5136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) ◇ (X4 ◇ (X5 ◇ X0)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq11 eq10
  have eq46 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ (X4 ◇ (X5 ◇ X0)))) = X5 := superpose eq34 eq9
  have eq72 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ (X4 ◇ (X5 ◇ X0))) = X5 := superpose eq34 eq46
  have eq73 (X0 X1 X3 X5 : G) : ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ (X5 ◇ X0)) = X5 := superpose eq34 eq72
  have eq74 (X0 X1 X3 X5 : G) : ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X0) = X5 := superpose eq34 eq73
  have eq75 (X0 X1 X3 X5 : G) : ((X0 ◇ (X3 ◇ X1)) ◇ X0) = X5 := superpose eq34 eq74
  have eq76 (X0 X1 X3 X5 : G) : ((X3 ◇ X1) ◇ X0) = X5 := superpose eq34 eq75
  have eq77 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq34 eq76
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq77 eq77
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq80 eq78


@[equational_result]
theorem Equation5137_implies_Equation2 (G : Type*) [Magma G] (h : Equation5137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq53 eq17


@[equational_result]
theorem Equation5138_implies_Equation2 (G : Type*) [Magma G] (h : Equation5138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation5139_implies_Equation2 (G : Type*) [Magma G] (h : Equation5139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5143_implies_Equation2 (G : Type*) [Magma G] (h : Equation5143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5145_implies_Equation2 (G : Type*) [Magma G] (h : Equation5145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5146_implies_Equation2 (G : Type*) [Magma G] (h : Equation5146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5147_implies_Equation2 (G : Type*) [Magma G] (h : Equation5147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5149_implies_Equation2 (G : Type*) [Magma G] (h : Equation5149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5150_implies_Equation2 (G : Type*) [Magma G] (h : Equation5150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5151_implies_Equation2 (G : Type*) [Magma G] (h : Equation5151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5153_implies_Equation2 (G : Type*) [Magma G] (h : Equation5153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5154_implies_Equation2 (G : Type*) [Magma G] (h : Equation5154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5155_implies_Equation2 (G : Type*) [Magma G] (h : Equation5155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5156_implies_Equation2 (G : Type*) [Magma G] (h : Equation5156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5158_implies_Equation2 (G : Type*) [Magma G] (h : Equation5158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq11
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq11 eq14
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq48 eq28


@[equational_result]
theorem Equation5159_implies_Equation2 (G : Type*) [Magma G] (h : Equation5159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq52 eq15


@[equational_result]
theorem Equation5160_implies_Equation2 (G : Type*) [Magma G] (h : Equation5160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq12 eq10
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq12 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation5162_implies_Equation2 (G : Type*) [Magma G] (h : Equation5162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5163_implies_Equation2 (G : Type*) [Magma G] (h : Equation5163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5164_implies_Equation2 (G : Type*) [Magma G] (h : Equation5164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5166_implies_Equation2 (G : Type*) [Magma G] (h : Equation5166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5167_implies_Equation2 (G : Type*) [Magma G] (h : Equation5167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5168_implies_Equation2 (G : Type*) [Magma G] (h : Equation5168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5170_implies_Equation2 (G : Type*) [Magma G] (h : Equation5170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5171_implies_Equation2 (G : Type*) [Magma G] (h : Equation5171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5172_implies_Equation2 (G : Type*) [Magma G] (h : Equation5172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5173_implies_Equation2 (G : Type*) [Magma G] (h : Equation5173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5175_implies_Equation2 (G : Type*) [Magma G] (h : Equation5175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation5176_implies_Equation2 (G : Type*) [Magma G] (h : Equation5176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq48 eq16


@[equational_result]
theorem Equation5177_implies_Equation2 (G : Type*) [Magma G] (h : Equation5177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5178_implies_Equation2 (G : Type*) [Magma G] (h : Equation5178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5180_implies_Equation2 (G : Type*) [Magma G] (h : Equation5180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5181_implies_Equation2 (G : Type*) [Magma G] (h : Equation5181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5182_implies_Equation2 (G : Type*) [Magma G] (h : Equation5182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5183_implies_Equation2 (G : Type*) [Magma G] (h : Equation5183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5185_implies_Equation2 (G : Type*) [Magma G] (h : Equation5185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5186_implies_Equation2 (G : Type*) [Magma G] (h : Equation5186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5187_implies_Equation2 (G : Type*) [Magma G] (h : Equation5187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5188_implies_Equation2 (G : Type*) [Magma G] (h : Equation5188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5190_implies_Equation2 (G : Type*) [Magma G] (h : Equation5190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5191_implies_Equation2 (G : Type*) [Magma G] (h : Equation5191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5192_implies_Equation2 (G : Type*) [Magma G] (h : Equation5192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5193_implies_Equation2 (G : Type*) [Magma G] (h : Equation5193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5195_implies_Equation2 (G : Type*) [Magma G] (h : Equation5195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5196_implies_Equation2 (G : Type*) [Magma G] (h : Equation5196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5197_implies_Equation2 (G : Type*) [Magma G] (h : Equation5197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5198_implies_Equation2 (G : Type*) [Magma G] (h : Equation5198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5199_implies_Equation2 (G : Type*) [Magma G] (h : Equation5199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5201_implies_Equation2 (G : Type*) [Magma G] (h : Equation5201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq13 eq7
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq20
  have eq34 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq33
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq34
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation5202_implies_Equation2 (G : Type*) [Magma G] (h : Equation5202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := superpose eq12 eq9
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation5203_implies_Equation2 (G : Type*) [Magma G] (h : Equation5203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq9 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq13 eq9
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq13 eq14
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5205_implies_Equation2 (G : Type*) [Magma G] (h : Equation5205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq10 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq10 eq12
  have eq24 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq9
  have eq26 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq9 eq7
  have eq33 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq24
  have eq34 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq33 eq10
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq34 eq7
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq26 eq35
  have eq63 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq54
  have eq64 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq26 eq63
  have eq87 (X0 X2 : G) : X0 = X2 := superpose eq64 eq64
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq89 eq87


@[equational_result]
theorem Equation5206_implies_Equation2 (G : Type*) [Magma G] (h : Equation5206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq11 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq11 eq7
  have eq37 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq11
  have eq69 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq37
  have eq75 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) = X3 := superpose eq37 eq9
  have eq76 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq37 eq10
  have eq108 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq13
  have eq110 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq13 eq7
  have eq120 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq69 eq108
  have eq123 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq120 eq69
  have eq127 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq123 eq37
  have eq154 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq127 eq110
  have eq158 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq123 eq154
  have eq159 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq158 eq11
  have eq160 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq158 eq12
  have eq223 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq159 eq76
  have eq224 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) = X3 := superpose eq159 eq75
  have eq240 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq160 eq223
  have eq241 (X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) = X3 := superpose eq240 eq224
  have eq271 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq240 eq241
  have eq272 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq240 eq271
  have eq273 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = X3 := superpose eq240 eq272
  have eq274 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq240 eq273
  have eq275 (X0 X1 : G) : X0 = X1 := superpose eq158 eq274
  have eq283 (X0 : G) : sK0 ≠ X0 := superpose eq275 eq8
  subsumption eq283 eq275


@[equational_result]
theorem Equation5207_implies_Equation2 (G : Type*) [Magma G] (h : Equation5207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq13 eq10
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5210_implies_Equation2 (G : Type*) [Magma G] (h : Equation5210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq16 eq7
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq16 eq19
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq16 eq27
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq16 eq28
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation5211_implies_Equation2 (G : Type*) [Magma G] (h : Equation5211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq13 eq10
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5213_implies_Equation2 (G : Type*) [Magma G] (h : Equation5213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ (X5 ◇ X0)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq7 eq12
  have eq21 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X5 ◇ (X5 ◇ X0)))) = X5 := superpose eq13 eq9
  have eq26 (X0 X2 X3 X5 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X5 ◇ (X5 ◇ X0))) = X5 := superpose eq13 eq21
  have eq27 (X0 X2 X3 X5 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X5 ◇ X0)) = X5 := superpose eq13 eq26
  have eq28 (X0 X2 X3 X5 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X5 := superpose eq13 eq27
  have eq29 (X0 X2 X3 X5 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ X0) = X5 := superpose eq13 eq28
  have eq30 (X0 X2 X3 X5 : G) : ((X2 ◇ X3) ◇ X0) = X5 := superpose eq13 eq29
  have eq31 (X0 X3 X5 : G) : (X3 ◇ X0) = X5 := superpose eq13 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation5214_implies_Equation2 (G : Type*) [Magma G] (h : Equation5214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ (X4 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X3 ◇ X2))) ◇ (X4 ◇ (X4 ◇ X0)))) = X4 := superpose eq12 eq9
  have eq17 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq12 eq13
  have eq18 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X4 := superpose eq12 eq17
  have eq19 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation5215_implies_Equation2 (G : Type*) [Magma G] (h : Equation5215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq12 eq10
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation5216_implies_Equation2 (G : Type*) [Magma G] (h : Equation5216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq13 eq10
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5218_implies_Equation2 (G : Type*) [Magma G] (h : Equation5218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))))) ◇ X0) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X0 := superpose eq9 eq9
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq7
  have eq31 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq21
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq31 eq26
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = (X0 ◇ X0) := superpose eq33 eq11
  have eq49 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq7
  have eq56 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq49 eq31
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq56 eq33
  have eq65 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq62 eq13
  have eq67 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq62 eq65
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq67 eq67
  have eq86 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq86 eq73


@[equational_result]
theorem Equation5220_implies_Equation2 (G : Type*) [Magma G] (h : Equation5220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5222_implies_Equation2 (G : Type*) [Magma G] (h : Equation5222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq31 eq15


@[equational_result]
theorem Equation5224_implies_Equation2 (G : Type*) [Magma G] (h : Equation5224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5226_implies_Equation2 (G : Type*) [Magma G] (h : Equation5226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq10 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq74 eq26


@[equational_result]
theorem Equation5227_implies_Equation2 (G : Type*) [Magma G] (h : Equation5227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq32 eq11


@[equational_result]
theorem Equation5228_implies_Equation2 (G : Type*) [Magma G] (h : Equation5228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5230_implies_Equation2 (G : Type*) [Magma G] (h : Equation5230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation5231_implies_Equation2 (G : Type*) [Magma G] (h : Equation5231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq42 eq13


@[equational_result]
theorem Equation5232_implies_Equation2 (G : Type*) [Magma G] (h : Equation5232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5233_implies_Equation2 (G : Type*) [Magma G] (h : Equation5233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5235_implies_Equation2 (G : Type*) [Magma G] (h : Equation5235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq34 eq14


@[equational_result]
theorem Equation5236_implies_Equation2 (G : Type*) [Magma G] (h : Equation5236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq123 eq40


@[equational_result]
theorem Equation5237_implies_Equation2 (G : Type*) [Magma G] (h : Equation5237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5240_implies_Equation2 (G : Type*) [Magma G] (h : Equation5240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X2 := superpose eq9 eq9
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq15 eq7
  have eq45 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := superpose eq26 eq15
  have eq57 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq26 eq7
  have eq88 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X1)) = X1 := superpose eq57 eq45
  have eq103 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X1 := superpose eq57 eq88
  have eq104 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0)) = X3 := superpose eq103 eq9
  have eq132 (X0 X4 : G) : X0 = X4 := superpose eq104 eq104
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq132 eq8
  subsumption eq142 eq132


@[equational_result]
theorem Equation5241_implies_Equation2 (G : Type*) [Magma G] (h : Equation5241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5244_implies_Equation2 (G : Type*) [Magma G] (h : Equation5244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq9
  have eq23 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq14
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq23 eq7
  have eq34 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq23 eq14
  have eq43 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X1 := superpose eq28 eq34
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq66 eq56


@[equational_result]
theorem Equation5245_implies_Equation2 (G : Type*) [Magma G] (h : Equation5245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5247_implies_Equation2 (G : Type*) [Magma G] (h : Equation5247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq48 eq16


@[equational_result]
theorem Equation5248_implies_Equation2 (G : Type*) [Magma G] (h : Equation5248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X4 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X0)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)))) = X4 := superpose eq11 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) = X4 := superpose eq11 eq12
  have eq16 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq11 eq15
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq28 eq21


@[equational_result]
theorem Equation5249_implies_Equation2 (G : Type*) [Magma G] (h : Equation5249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq124 eq45


@[equational_result]
theorem Equation5250_implies_Equation2 (G : Type*) [Magma G] (h : Equation5250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5252_implies_Equation2 (G : Type*) [Magma G] (h : Equation5252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation5253_implies_Equation2 (G : Type*) [Magma G] (h : Equation5253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation5254_implies_Equation2 (G : Type*) [Magma G] (h : Equation5254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5255_implies_Equation2 (G : Type*) [Magma G] (h : Equation5255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5257_implies_Equation2 (G : Type*) [Magma G] (h : Equation5257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation5258_implies_Equation2 (G : Type*) [Magma G] (h : Equation5258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ (X4 ◇ (X5 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X0))) = X4 := superpose eq11 eq7
  have eq21 (X1 X4 X5 : G) : (X1 ◇ X5) = X4 := superpose eq18 eq9
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq44 eq22


@[equational_result]
theorem Equation5259_implies_Equation2 (G : Type*) [Magma G] (h : Equation5259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation5260_implies_Equation2 (G : Type*) [Magma G] (h : Equation5260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5262_implies_Equation2 (G : Type*) [Magma G] (h : Equation5262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation5263_implies_Equation2 (G : Type*) [Magma G] (h : Equation5263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation5264_implies_Equation2 (G : Type*) [Magma G] (h : Equation5264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5265_implies_Equation2 (G : Type*) [Magma G] (h : Equation5265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5267_implies_Equation2 (G : Type*) [Magma G] (h : Equation5267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation5268_implies_Equation2 (G : Type*) [Magma G] (h : Equation5268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation5269_implies_Equation2 (G : Type*) [Magma G] (h : Equation5269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5270_implies_Equation2 (G : Type*) [Magma G] (h : Equation5270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5272_implies_Equation2 (G : Type*) [Magma G] (h : Equation5272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation5273_implies_Equation2 (G : Type*) [Magma G] (h : Equation5273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation5274_implies_Equation2 (G : Type*) [Magma G] (h : Equation5274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5275_implies_Equation2 (G : Type*) [Magma G] (h : Equation5275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5276_implies_Equation2 (G : Type*) [Magma G] (h : Equation5276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5278_implies_Equation2 (G : Type*) [Magma G] (h : Equation5278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq11 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq13 eq7
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq35 eq7
  have eq62 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq35 eq39
  have eq63 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq35 eq62
  have eq64 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq35 eq63
  have eq138 (X0 X2 : G) : X0 = X2 := superpose eq64 eq64
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq140 eq138


@[equational_result]
theorem Equation5280_implies_Equation2 (G : Type*) [Magma G] (h : Equation5280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5282_implies_Equation2 (G : Type*) [Magma G] (h : Equation5282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X1))) = X0 := superpose eq11 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq26 eq20


@[equational_result]
theorem Equation5284_implies_Equation2 (G : Type*) [Magma G] (h : Equation5284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation5288_implies_Equation2 (G : Type*) [Magma G] (h : Equation5288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation5290_implies_Equation2 (G : Type*) [Magma G] (h : Equation5290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq38 eq16


@[equational_result]
theorem Equation5291_implies_Equation2 (G : Type*) [Magma G] (h : Equation5291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq124 eq48


@[equational_result]
theorem Equation5292_implies_Equation2 (G : Type*) [Magma G] (h : Equation5292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation5293_implies_Equation2 (G : Type*) [Magma G] (h : Equation5293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5297_implies_Equation2 (G : Type*) [Magma G] (h : Equation5297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5299_implies_Equation2 (G : Type*) [Magma G] (h : Equation5299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5300_implies_Equation2 (G : Type*) [Magma G] (h : Equation5300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5301_implies_Equation2 (G : Type*) [Magma G] (h : Equation5301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5303_implies_Equation2 (G : Type*) [Magma G] (h : Equation5303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5304_implies_Equation2 (G : Type*) [Magma G] (h : Equation5304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5305_implies_Equation2 (G : Type*) [Magma G] (h : Equation5305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5307_implies_Equation2 (G : Type*) [Magma G] (h : Equation5307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5308_implies_Equation2 (G : Type*) [Magma G] (h : Equation5308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5309_implies_Equation2 (G : Type*) [Magma G] (h : Equation5309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5310_implies_Equation2 (G : Type*) [Magma G] (h : Equation5310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5312_implies_Equation2 (G : Type*) [Magma G] (h : Equation5312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X0)))) = X2 := superpose eq12 eq9
  have eq20 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq12 eq16
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation5313_implies_Equation2 (G : Type*) [Magma G] (h : Equation5313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X3 := superpose eq10 eq9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq10 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation5314_implies_Equation2 (G : Type*) [Magma G] (h : Equation5314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5316_implies_Equation2 (G : Type*) [Magma G] (h : Equation5316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5317_implies_Equation2 (G : Type*) [Magma G] (h : Equation5317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5318_implies_Equation2 (G : Type*) [Magma G] (h : Equation5318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5320_implies_Equation2 (G : Type*) [Magma G] (h : Equation5320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5321_implies_Equation2 (G : Type*) [Magma G] (h : Equation5321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5322_implies_Equation2 (G : Type*) [Magma G] (h : Equation5322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5324_implies_Equation2 (G : Type*) [Magma G] (h : Equation5324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5325_implies_Equation2 (G : Type*) [Magma G] (h : Equation5325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5326_implies_Equation2 (G : Type*) [Magma G] (h : Equation5326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5327_implies_Equation2 (G : Type*) [Magma G] (h : Equation5327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5329_implies_Equation2 (G : Type*) [Magma G] (h : Equation5329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq59 eq15


@[equational_result]
theorem Equation5330_implies_Equation2 (G : Type*) [Magma G] (h : Equation5330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation5331_implies_Equation2 (G : Type*) [Magma G] (h : Equation5331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X5)))) ◇ X0)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X4 := superpose eq10 eq9
  have eq14 (X1 X2 X4 : G) : (X1 ◇ X2) = X4 := superpose eq10 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation5332_implies_Equation2 (G : Type*) [Magma G] (h : Equation5332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5334_implies_Equation2 (G : Type*) [Magma G] (h : Equation5334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5335_implies_Equation2 (G : Type*) [Magma G] (h : Equation5335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5336_implies_Equation2 (G : Type*) [Magma G] (h : Equation5336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5337_implies_Equation2 (G : Type*) [Magma G] (h : Equation5337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5339_implies_Equation2 (G : Type*) [Magma G] (h : Equation5339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5340_implies_Equation2 (G : Type*) [Magma G] (h : Equation5340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5341_implies_Equation2 (G : Type*) [Magma G] (h : Equation5341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5342_implies_Equation2 (G : Type*) [Magma G] (h : Equation5342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5344_implies_Equation2 (G : Type*) [Magma G] (h : Equation5344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5345_implies_Equation2 (G : Type*) [Magma G] (h : Equation5345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5346_implies_Equation2 (G : Type*) [Magma G] (h : Equation5346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5347_implies_Equation2 (G : Type*) [Magma G] (h : Equation5347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5349_implies_Equation2 (G : Type*) [Magma G] (h : Equation5349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5350_implies_Equation2 (G : Type*) [Magma G] (h : Equation5350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5351_implies_Equation2 (G : Type*) [Magma G] (h : Equation5351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5352_implies_Equation2 (G : Type*) [Magma G] (h : Equation5352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5353_implies_Equation2 (G : Type*) [Magma G] (h : Equation5353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5355_implies_Equation2 (G : Type*) [Magma G] (h : Equation5355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq42 eq28


@[equational_result]
theorem Equation5356_implies_Equation2 (G : Type*) [Magma G] (h : Equation5356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3)))) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq11
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = ((X3 ◇ (X3 ◇ X0)) ◇ X3) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq11 eq11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq12
  have eq23 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = X0 := superpose eq20 eq13
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq23 eq11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq24 eq15
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq24 eq25
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation5357_implies_Equation2 (G : Type*) [Magma G] (h : Equation5357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation5360_implies_Equation2 (G : Type*) [Magma G] (h : Equation5360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq10 eq10
  have eq16 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := superpose eq10 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := superpose eq10 eq9
  have eq55 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))))) := superpose eq16 eq15
  have eq56 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq15
  have eq66 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq7 eq55
  have eq68 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)))) = X1 := superpose eq56 eq9
  have eq70 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq56 eq7
  have eq83 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq70 eq56
  have eq86 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose eq83 eq68
  have eq90 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq83 eq86
  have eq162 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq83 eq7
  have eq175 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq162 eq15
  have eq201 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq16 eq175
  have eq206 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose eq175 eq7
  have eq209 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) = X0 := superpose eq175 eq7
  have eq249 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq83 eq201
  have eq250 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq66 eq249
  have eq266 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq16 eq90
  have eq290 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq250 eq266
  have eq291 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq83 eq290
  have eq292 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq83 eq291
  have eq294 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))))) = X2 := superpose eq292 eq25
  have eq338 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X2 := superpose eq292 eq294
  have eq346 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq338 eq209
  have eq388 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq346 eq206
  have eq397 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := superpose eq388 eq7
  have eq417 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq388 eq397
  have eq418 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq388 eq417
  have eq419 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq388 eq418
  have eq420 (X0 X1 : G) : X0 = X1 := superpose eq83 eq419
  have eq425 (X0 : G) : sK0 ≠ X0 := superpose eq420 eq8
  subsumption eq425 eq420


@[equational_result]
theorem Equation5361_implies_Equation2 (G : Type*) [Magma G] (h : Equation5361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5364_implies_Equation2 (G : Type*) [Magma G] (h : Equation5364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X2)))) ◇ X0)) = X3 := superpose eq7 eq9
  have eq24 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq14
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq140 eq34


@[equational_result]
theorem Equation5365_implies_Equation2 (G : Type*) [Magma G] (h : Equation5365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5367_implies_Equation2 (G : Type*) [Magma G] (h : Equation5367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation5368_implies_Equation2 (G : Type*) [Magma G] (h : Equation5368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X0))) = X4 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq56 eq39


@[equational_result]
theorem Equation5369_implies_Equation2 (G : Type*) [Magma G] (h : Equation5369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation5370_implies_Equation2 (G : Type*) [Magma G] (h : Equation5370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5372_implies_Equation2 (G : Type*) [Magma G] (h : Equation5372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq10 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))) ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))))) ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))))))) := superpose eq9 eq15
  have eq51 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq16
  have eq70 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq51 eq7
  have eq87 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) = (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq10 eq12
  have eq111 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq70 eq87
  have eq122 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))) ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3)))))) := superpose eq111 eq31
  have eq125 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = X0 := superpose eq70 eq122
  have eq126 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq125 eq7
  have eq210 (X0 X2 : G) : X0 = X2 := superpose eq126 eq126
  have eq212 (X0 : G) : sK0 ≠ X0 := superpose eq210 eq8
  subsumption eq212 eq210


@[equational_result]
theorem Equation5374_implies_Equation2 (G : Type*) [Magma G] (h : Equation5374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5376_implies_Equation2 (G : Type*) [Magma G] (h : Equation5376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5377_implies_Equation2 (G : Type*) [Magma G] (h : Equation5377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5378_implies_Equation2 (G : Type*) [Magma G] (h : Equation5378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5380_implies_Equation2 (G : Type*) [Magma G] (h : Equation5380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5381_implies_Equation2 (G : Type*) [Magma G] (h : Equation5381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5382_implies_Equation2 (G : Type*) [Magma G] (h : Equation5382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5384_implies_Equation2 (G : Type*) [Magma G] (h : Equation5384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5385_implies_Equation2 (G : Type*) [Magma G] (h : Equation5385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5386_implies_Equation2 (G : Type*) [Magma G] (h : Equation5386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5387_implies_Equation2 (G : Type*) [Magma G] (h : Equation5387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5390_implies_Equation2 (G : Type*) [Magma G] (h : Equation5390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq9 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation5391_implies_Equation2 (G : Type*) [Magma G] (h : Equation5391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5393_implies_Equation2 (G : Type*) [Magma G] (h : Equation5393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5394_implies_Equation2 (G : Type*) [Magma G] (h : Equation5394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5395_implies_Equation2 (G : Type*) [Magma G] (h : Equation5395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5397_implies_Equation2 (G : Type*) [Magma G] (h : Equation5397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5398_implies_Equation2 (G : Type*) [Magma G] (h : Equation5398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5399_implies_Equation2 (G : Type*) [Magma G] (h : Equation5399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5401_implies_Equation2 (G : Type*) [Magma G] (h : Equation5401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5402_implies_Equation2 (G : Type*) [Magma G] (h : Equation5402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5403_implies_Equation2 (G : Type*) [Magma G] (h : Equation5403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5404_implies_Equation2 (G : Type*) [Magma G] (h : Equation5404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5406_implies_Equation2 (G : Type*) [Magma G] (h : Equation5406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation5407_implies_Equation2 (G : Type*) [Magma G] (h : Equation5407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X4)))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq7 eq11
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = ((X4 ◇ (X5 ◇ X0)) ◇ X5) := superpose eq11 eq11
  have eq15 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq15 eq12
  have eq24 (X0 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ X5) = X0 := superpose eq21 eq13
  have eq26 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq24 eq11
  have eq27 (X0 X1 X3 X4 : G) : (X1 ◇ (X3 ◇ (X4 ◇ X0))) = X4 := superpose eq26 eq15
  have eq31 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X4 := superpose eq26 eq27
  have eq32 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq26 eq31
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq38 eq33


@[equational_result]
theorem Equation5408_implies_Equation2 (G : Type*) [Magma G] (h : Equation5408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation5409_implies_Equation2 (G : Type*) [Magma G] (h : Equation5409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5411_implies_Equation2 (G : Type*) [Magma G] (h : Equation5411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5412_implies_Equation2 (G : Type*) [Magma G] (h : Equation5412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5413_implies_Equation2 (G : Type*) [Magma G] (h : Equation5413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5414_implies_Equation2 (G : Type*) [Magma G] (h : Equation5414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5416_implies_Equation2 (G : Type*) [Magma G] (h : Equation5416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5417_implies_Equation2 (G : Type*) [Magma G] (h : Equation5417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5418_implies_Equation2 (G : Type*) [Magma G] (h : Equation5418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5419_implies_Equation2 (G : Type*) [Magma G] (h : Equation5419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5421_implies_Equation2 (G : Type*) [Magma G] (h : Equation5421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5422_implies_Equation2 (G : Type*) [Magma G] (h : Equation5422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5423_implies_Equation2 (G : Type*) [Magma G] (h : Equation5423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5424_implies_Equation2 (G : Type*) [Magma G] (h : Equation5424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5426_implies_Equation2 (G : Type*) [Magma G] (h : Equation5426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5427_implies_Equation2 (G : Type*) [Magma G] (h : Equation5427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5428_implies_Equation2 (G : Type*) [Magma G] (h : Equation5428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5429_implies_Equation2 (G : Type*) [Magma G] (h : Equation5429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5430_implies_Equation2 (G : Type*) [Magma G] (h : Equation5430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5432_implies_Equation2 (G : Type*) [Magma G] (h : Equation5432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq19 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq13 eq7
  have eq29 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq19
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq29
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq30
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation5433_implies_Equation2 (G : Type*) [Magma G] (h : Equation5433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ (X5 ◇ X0)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X4 ◇ (X5 ◇ X0)))) = X5 := superpose eq12 eq9
  have eq17 (X0 X1 X4 X5 : G) : (X1 ◇ (X4 ◇ (X5 ◇ X0))) = X5 := superpose eq12 eq13
  have eq18 (X0 X1 X5 : G) : (X1 ◇ (X5 ◇ X0)) = X5 := superpose eq12 eq17
  have eq19 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation5434_implies_Equation2 (G : Type*) [Magma G] (h : Equation5434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X4)))) ◇ (X5 ◇ X0)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X4 ◇ (X0 ◇ (X0 ◇ X4))) ◇ (X5 ◇ X0)))) = X5 := superpose eq12 eq9
  have eq17 (X0 X1 X4 X5 : G) : (X1 ◇ ((X4 ◇ (X0 ◇ (X0 ◇ X4))) ◇ (X5 ◇ X0))) = X5 := superpose eq12 eq13
  have eq18 (X0 X1 X5 : G) : (X1 ◇ (X5 ◇ X0)) = X5 := superpose eq12 eq17
  have eq19 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation5435_implies_Equation2 (G : Type*) [Magma G] (h : Equation5435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq9 eq7
  have eq14 (X0 X1 X3 X4 : G) : (X1 ◇ (X3 ◇ (X4 ◇ X0))) = X4 := superpose eq13 eq9
  have eq15 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X4 := superpose eq13 eq14
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation5437_implies_Equation2 (G : Type*) [Magma G] (h : Equation5437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq56 eq14


@[equational_result]
theorem Equation5438_implies_Equation2 (G : Type*) [Magma G] (h : Equation5438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq11 eq11
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq134 eq43


@[equational_result]
theorem Equation5439_implies_Equation2 (G : Type*) [Magma G] (h : Equation5439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation5440_implies_Equation2 (G : Type*) [Magma G] (h : Equation5440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5442_implies_Equation2 (G : Type*) [Magma G] (h : Equation5442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation5443_implies_Equation2 (G : Type*) [Magma G] (h : Equation5443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation5444_implies_Equation2 (G : Type*) [Magma G] (h : Equation5444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq68 eq15


@[equational_result]
theorem Equation5445_implies_Equation2 (G : Type*) [Magma G] (h : Equation5445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5447_implies_Equation2 (G : Type*) [Magma G] (h : Equation5447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation5448_implies_Equation2 (G : Type*) [Magma G] (h : Equation5448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation5449_implies_Equation2 (G : Type*) [Magma G] (h : Equation5449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X3))) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5450_implies_Equation2 (G : Type*) [Magma G] (h : Equation5450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5452_implies_Equation2 (G : Type*) [Magma G] (h : Equation5452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation5453_implies_Equation2 (G : Type*) [Magma G] (h : Equation5453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation5454_implies_Equation2 (G : Type*) [Magma G] (h : Equation5454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5455_implies_Equation2 (G : Type*) [Magma G] (h : Equation5455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5456_implies_Equation2 (G : Type*) [Magma G] (h : Equation5456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5458_implies_Equation2 (G : Type*) [Magma G] (h : Equation5458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq11 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq11 eq16
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation5459_implies_Equation2 (G : Type*) [Magma G] (h : Equation5459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq59 eq42


@[equational_result]
theorem Equation5460_implies_Equation2 (G : Type*) [Magma G] (h : Equation5460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation5461_implies_Equation2 (G : Type*) [Magma G] (h : Equation5461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5463_implies_Equation2 (G : Type*) [Magma G] (h : Equation5463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5464_implies_Equation2 (G : Type*) [Magma G] (h : Equation5464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5465_implies_Equation2 (G : Type*) [Magma G] (h : Equation5465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5466_implies_Equation2 (G : Type*) [Magma G] (h : Equation5466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5468_implies_Equation2 (G : Type*) [Magma G] (h : Equation5468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5469_implies_Equation2 (G : Type*) [Magma G] (h : Equation5469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5470_implies_Equation2 (G : Type*) [Magma G] (h : Equation5470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5471_implies_Equation2 (G : Type*) [Magma G] (h : Equation5471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5473_implies_Equation2 (G : Type*) [Magma G] (h : Equation5473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5474_implies_Equation2 (G : Type*) [Magma G] (h : Equation5474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5475_implies_Equation2 (G : Type*) [Magma G] (h : Equation5475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5476_implies_Equation2 (G : Type*) [Magma G] (h : Equation5476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5478_implies_Equation2 (G : Type*) [Magma G] (h : Equation5478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5479_implies_Equation2 (G : Type*) [Magma G] (h : Equation5479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5480_implies_Equation2 (G : Type*) [Magma G] (h : Equation5480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5481_implies_Equation2 (G : Type*) [Magma G] (h : Equation5481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5482_implies_Equation2 (G : Type*) [Magma G] (h : Equation5482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5484_implies_Equation2 (G : Type*) [Magma G] (h : Equation5484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation5485_implies_Equation2 (G : Type*) [Magma G] (h : Equation5485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation5486_implies_Equation2 (G : Type*) [Magma G] (h : Equation5486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation5487_implies_Equation2 (G : Type*) [Magma G] (h : Equation5487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5489_implies_Equation2 (G : Type*) [Magma G] (h : Equation5489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5490_implies_Equation2 (G : Type*) [Magma G] (h : Equation5490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5491_implies_Equation2 (G : Type*) [Magma G] (h : Equation5491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5492_implies_Equation2 (G : Type*) [Magma G] (h : Equation5492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5494_implies_Equation2 (G : Type*) [Magma G] (h : Equation5494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5495_implies_Equation2 (G : Type*) [Magma G] (h : Equation5495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5496_implies_Equation2 (G : Type*) [Magma G] (h : Equation5496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5497_implies_Equation2 (G : Type*) [Magma G] (h : Equation5497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5499_implies_Equation2 (G : Type*) [Magma G] (h : Equation5499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5500_implies_Equation2 (G : Type*) [Magma G] (h : Equation5500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5501_implies_Equation2 (G : Type*) [Magma G] (h : Equation5501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5502_implies_Equation2 (G : Type*) [Magma G] (h : Equation5502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5504_implies_Equation2 (G : Type*) [Magma G] (h : Equation5504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5505_implies_Equation2 (G : Type*) [Magma G] (h : Equation5505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5506_implies_Equation2 (G : Type*) [Magma G] (h : Equation5506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5507_implies_Equation2 (G : Type*) [Magma G] (h : Equation5507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5508_implies_Equation2 (G : Type*) [Magma G] (h : Equation5508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5510_implies_Equation2 (G : Type*) [Magma G] (h : Equation5510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation5511_implies_Equation2 (G : Type*) [Magma G] (h : Equation5511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation5512_implies_Equation2 (G : Type*) [Magma G] (h : Equation5512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq69 eq15


@[equational_result]
theorem Equation5513_implies_Equation2 (G : Type*) [Magma G] (h : Equation5513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5515_implies_Equation2 (G : Type*) [Magma G] (h : Equation5515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5516_implies_Equation2 (G : Type*) [Magma G] (h : Equation5516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5517_implies_Equation2 (G : Type*) [Magma G] (h : Equation5517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5518_implies_Equation2 (G : Type*) [Magma G] (h : Equation5518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5520_implies_Equation2 (G : Type*) [Magma G] (h : Equation5520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5521_implies_Equation2 (G : Type*) [Magma G] (h : Equation5521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5522_implies_Equation2 (G : Type*) [Magma G] (h : Equation5522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5523_implies_Equation2 (G : Type*) [Magma G] (h : Equation5523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5525_implies_Equation2 (G : Type*) [Magma G] (h : Equation5525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5526_implies_Equation2 (G : Type*) [Magma G] (h : Equation5526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5527_implies_Equation2 (G : Type*) [Magma G] (h : Equation5527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5528_implies_Equation2 (G : Type*) [Magma G] (h : Equation5528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5530_implies_Equation2 (G : Type*) [Magma G] (h : Equation5530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5531_implies_Equation2 (G : Type*) [Magma G] (h : Equation5531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5532_implies_Equation2 (G : Type*) [Magma G] (h : Equation5532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5533_implies_Equation2 (G : Type*) [Magma G] (h : Equation5533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5534_implies_Equation2 (G : Type*) [Magma G] (h : Equation5534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5536_implies_Equation2 (G : Type*) [Magma G] (h : Equation5536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation5537_implies_Equation2 (G : Type*) [Magma G] (h : Equation5537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq56 eq13


@[equational_result]
theorem Equation5538_implies_Equation2 (G : Type*) [Magma G] (h : Equation5538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5539_implies_Equation2 (G : Type*) [Magma G] (h : Equation5539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5540_implies_Equation2 (G : Type*) [Magma G] (h : Equation5540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation5542_implies_Equation2 (G : Type*) [Magma G] (h : Equation5542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5543_implies_Equation2 (G : Type*) [Magma G] (h : Equation5543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5544_implies_Equation2 (G : Type*) [Magma G] (h : Equation5544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5545_implies_Equation2 (G : Type*) [Magma G] (h : Equation5545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5546_implies_Equation2 (G : Type*) [Magma G] (h : Equation5546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5548_implies_Equation2 (G : Type*) [Magma G] (h : Equation5548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5549_implies_Equation2 (G : Type*) [Magma G] (h : Equation5549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5550_implies_Equation2 (G : Type*) [Magma G] (h : Equation5550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5551_implies_Equation2 (G : Type*) [Magma G] (h : Equation5551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5552_implies_Equation2 (G : Type*) [Magma G] (h : Equation5552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5554_implies_Equation2 (G : Type*) [Magma G] (h : Equation5554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5555_implies_Equation2 (G : Type*) [Magma G] (h : Equation5555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5556_implies_Equation2 (G : Type*) [Magma G] (h : Equation5556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5557_implies_Equation2 (G : Type*) [Magma G] (h : Equation5557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5558_implies_Equation2 (G : Type*) [Magma G] (h : Equation5558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5560_implies_Equation2 (G : Type*) [Magma G] (h : Equation5560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5561_implies_Equation2 (G : Type*) [Magma G] (h : Equation5561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5562_implies_Equation2 (G : Type*) [Magma G] (h : Equation5562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5563_implies_Equation2 (G : Type*) [Magma G] (h : Equation5563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5564_implies_Equation2 (G : Type*) [Magma G] (h : Equation5564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5566_implies_Equation2 (G : Type*) [Magma G] (h : Equation5566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5567_implies_Equation2 (G : Type*) [Magma G] (h : Equation5567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5568_implies_Equation2 (G : Type*) [Magma G] (h : Equation5568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X3))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5569_implies_Equation2 (G : Type*) [Magma G] (h : Equation5569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X4))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5570_implies_Equation2 (G : Type*) [Magma G] (h : Equation5570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X5))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5571_implies_Equation2 (G : Type*) [Magma G] (h : Equation5571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6))))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation5777_implies_Equation2 (G : Type*) [Magma G] (h : Equation5777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation5780_implies_Equation2 (G : Type*) [Magma G] (h : Equation5780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation5782_implies_Equation2 (G : Type*) [Magma G] (h : Equation5782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) ◇ (X2 ◇ X4)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1)))) := superpose eq7 eq17
  have eq44 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq17 eq17
  have eq52 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq17 eq9
  have eq54 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq17 eq52
  have eq55 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq54 eq11
  have eq62 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq55
  have eq79 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq44 eq62
  have eq80 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := superpose eq79 eq41
  have eq83 (X0 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X4)))) ◇ (X2 ◇ X0)) = X2 := superpose eq80 eq32
  have eq93 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq80 eq83
  have eq97 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq93 eq54
  have eq98 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X3 := superpose eq97 eq13
  have eq109 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq97 eq98
  have eq112 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq109 eq93
  have eq114 (X0 X1 : G) : X0 = X1 := superpose eq109 eq112
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq119 eq114


@[equational_result]
theorem Equation5783_implies_Equation2 (G : Type*) [Magma G] (h : Equation5783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq18 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq18 eq12
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation5784_implies_Equation2 (G : Type*) [Magma G] (h : Equation5784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq19 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation5787_implies_Equation2 (G : Type*) [Magma G] (h : Equation5787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq12 eq11
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation5790_implies_Equation2 (G : Type*) [Magma G] (h : Equation5790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq11
  have eq21 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq12 eq9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq21 eq12
  have eq25 (X0 X1 : G) : X0 = X1 := superpose eq20 eq24
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq33 eq25


@[equational_result]
theorem Equation5792_implies_Equation2 (G : Type*) [Magma G] (h : Equation5792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq7 eq9
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq19 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq15
  have eq20 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq15 eq7
  have eq23 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq15 eq7
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq15 eq9
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq15 eq23
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq15 eq24
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq19 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq19 eq9
  have eq32 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq26 eq30
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq26 eq31
  have eq43 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq14 eq7
  have eq44 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq14 eq9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq26 eq43
  have eq46 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq26 eq45
  have eq47 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq32 eq46
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq47 eq25
  have eq53 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := superpose eq49 eq7
  have eq56 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X0 := superpose eq49 eq53
  have eq57 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq26 eq44
  have eq58 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq26 eq57
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq33 eq58
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq59 eq26
  have eq63 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq61 eq20
  have eq68 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq63 eq47
  have eq70 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq68 eq14
  have eq73 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq68 eq56
  have eq75 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq70 eq68
  have eq81 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq75 eq73
  have eq86 (X0 X2 : G) : X0 = X2 := superpose eq81 eq81
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq91 eq86


@[equational_result]
theorem Equation5794_implies_Equation2 (G : Type*) [Magma G] (h : Equation5794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq10
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq12
  have eq17 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq13 eq11
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq16 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation5796_implies_Equation2 (G : Type*) [Magma G] (h : Equation5796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) := superpose eq10 eq7
  have eq26 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq11 eq11
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq11 eq7
  have eq40 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq23
  have eq107 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq40
  have eq108 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq40 eq40
  have eq113 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq40 eq7
  have eq156 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq35 eq40
  have eq246 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq108 eq107
  have eq263 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose eq107 eq40
  have eq283 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq246 eq26
  have eq302 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq107 eq263
  have eq303 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq107 eq302
  have eq304 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq246 eq303
  have eq307 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq304 eq113
  have eq342 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq304 eq307
  have eq346 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq342 eq156
  have eq347 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq342 eq346
  have eq367 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq347 eq283
  have eq387 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq347 eq367
  have eq397 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq387 eq7
  have eq457 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq387 eq397
  have eq458 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq387 eq457
  have eq459 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq387 eq458
  have eq678 (X0 X2 : G) : X0 = X2 := superpose eq459 eq459
  have eq680 (X0 : G) : sK0 ≠ X0 := superpose eq678 eq8
  subsumption eq680 eq678


@[equational_result]
theorem Equation5797_implies_Equation2 (G : Type*) [Magma G] (h : Equation5797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq18 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq18 eq11
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation5798_implies_Equation2 (G : Type*) [Magma G] (h : Equation5798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq12 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation5800_implies_Equation2 (G : Type*) [Magma G] (h : Equation5800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ X0) = X0 := superpose eq7 eq12
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X2 := superpose eq12 eq7
  have eq32 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq27
  have eq76 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) = X0 := superpose eq32 eq12
  have eq80 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq32 eq27
  have eq105 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq80 eq7
  have eq168 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq32 eq105
  have eq173 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq12 eq105
  have eq178 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq105 eq7
  have eq204 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ X0) = X0 := superpose eq178 eq76
  have eq205 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq178 eq80
  have eq209 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq178 eq168
  have eq214 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq205 eq209
  have eq224 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose eq214 eq204
  have eq228 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq214 eq173
  have eq249 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq224 eq228
  have eq250 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq249
  have eq256 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq250 eq21
  have eq313 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))))) := superpose eq256 eq9
  have eq322 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) = ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))))) := superpose eq256 eq313
  have eq337 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq214 eq7
  have eq348 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq214 eq337
  have eq351 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq348 eq250
  have eq352 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq351 eq348
  have eq355 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq351 eq322
  have eq384 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq352 eq355
  have eq403 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq352 eq27
  have eq406 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq352 eq403
  have eq407 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq384 eq406
  have eq412 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq407 eq27
  have eq417 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq407 eq412
  have eq425 (X0 X3 : G) : X0 = X3 := superpose eq417 eq417
  have eq448 (X0 : G) : sK0 ≠ X0 := superpose eq425 eq8
  subsumption eq448 eq425


@[equational_result]
theorem Equation5801_implies_Equation2 (G : Type*) [Magma G] (h : Equation5801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X4 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X3))))))) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1))) ◇ X0) = X0 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) ◇ X2)))))) ◇ X1) = X1 := superpose eq16 eq16
  have eq24 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X4 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2)))))) = X4 := superpose eq16 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq16 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2))))))) = X1 := superpose eq16 eq7
  have eq30 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) ◇ X2))) = (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq16 eq7
  have eq31 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3))) = ((X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3))) ◇ (X0 ◇ X1))) := superpose eq16 eq9
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) ◇ X2))) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq16 eq30
  have eq35 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) ◇ X1) = X1 := superpose eq33 eq23
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3))) = ((X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq16 eq31
  have eq46 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) ◇ X0)) := superpose eq16 eq25
  have eq59 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X0) := superpose eq16 eq46
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3)))))) ◇ X2))) ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq14
  have eq73 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) := superpose eq16 eq14
  have eq87 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ ((X4 ◇ X0) ◇ X4))) ◇ X3))))) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq14 eq16
  have eq138 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq10
  have eq145 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2))) ◇ X0)) := superpose eq9 eq10
  have eq151 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1))) = (((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1))) ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1)))) := superpose eq9 eq10
  have eq178 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq138
  have eq185 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2))) ◇ X0)) := superpose eq16 eq138
  have eq186 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1))) ◇ X0) = X0 := superpose eq7 eq138
  have eq200 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq138 eq7
  have eq221 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq16 eq185
  have eq335 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ ((X3 ◇ (X3 ◇ ((X0 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) ◇ X0)) := superpose eq186 eq25
  have eq351 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3))) = ((X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ ((X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3))) ◇ (X0 ◇ X1))) := superpose eq186 eq9
  have eq353 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) := superpose eq186 eq335
  have eq365 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ (((X0 ◇ X1) ◇ ((X4 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3))) := superpose eq186 eq351
  have eq742 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq138 eq178
  have eq831 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq200 eq742
  have eq1216 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = X1 := superpose eq221 eq7
  have eq1309 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq1216 eq25
  have eq1357 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq64
  have eq1414 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq33 eq16
  have eq1439 (X0 X1 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X4 ◇ X1) ◇ X4))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq33 eq36
  have eq1444 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq36 eq16
  have eq1452 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq1414 eq186
  have eq1471 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2)))))) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq186 eq1444
  have eq1512 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq1452 eq178
  have eq1518 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq1512 eq1309
  have eq1521 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq1518 eq1357
  have eq1528 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) := superpose eq1521 eq73
  have eq1532 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq1521 eq200
  have eq1536 (X0 X1 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) = X0 := superpose eq1521 eq831
  have eq1557 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1521 eq1532
  have eq1583 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq1557 eq1536
  have eq1585 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2))) = X0 := superpose eq1583 eq221
  have eq1640 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq1585 eq28
  have eq1642 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X0) = X0 := superpose eq1585 eq59
  have eq1685 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq1557 eq1640
  have eq1689 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3))) = X0 := superpose eq1642 eq353
  have eq1699 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq1689 eq1471
  have eq1701 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq1689 eq365
  have eq1711 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq1557 eq1699
  have eq1712 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq1701 eq1439
  have eq1730 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1) = X1 := superpose eq1712 eq35
  have eq1760 (X0 X1 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X1 := superpose eq1557 eq1730
  have eq1761 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq1712 eq1760
  have eq1762 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq1712 eq1761
  have eq1763 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ X0) := superpose eq1762 eq1528
  have eq1766 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq1557 eq1763
  have eq1794 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3))))) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq1766 eq87
  have eq1810 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) ◇ X0)) := superpose eq1766 eq145
  have eq1813 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1))) = (((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1))) ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1)))) := superpose eq1766 eq151
  have eq2217 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)))))) ◇ (X0 ◇ X1)) := superpose eq1766 eq1794
  have eq2218 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ X1)) := superpose eq1766 eq2217
  have eq2242 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X2))) := superpose eq1766 eq1810
  have eq2243 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq1766 eq2242
  have eq2247 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq1766 eq1813
  have eq2248 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq2243 eq2247
  have eq2249 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq1766 eq2248
  have eq2264 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) ◇ (X0 ◇ X1)) := superpose eq2249 eq2218
  have eq2267 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq2249 eq2243
  have eq2283 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1685 eq2264
  have eq2286 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq2267 eq1711
  have eq2288 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq2286 eq2267
  have eq2322 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq2288 eq2283
  have eq2399 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1766 eq2322
  have eq2400 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq2399 eq1766
  have eq2427 (X0 X1 : G) : X0 = X1 := superpose eq2399 eq2400
  have eq2437 (X0 : G) : sK0 ≠ X0 := superpose eq2427 eq8
  subsumption eq2437 eq2427


@[equational_result]
theorem Equation5802_implies_Equation2 (G : Type*) [Magma G] (h : Equation5802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation5805_implies_Equation2 (G : Type*) [Magma G] (h : Equation5805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq12
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq13 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq13
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation5806_implies_Equation2 (G : Type*) [Magma G] (h : Equation5806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq12 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq42 eq17


@[equational_result]
theorem Equation5808_implies_Equation2 (G : Type*) [Magma G] (h : Equation5808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq50 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq18 eq9
  have eq52 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq18 eq50
  have eq60 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2))) := superpose eq11 eq11
  have eq67 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) = X2 := superpose eq18 eq11
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ ((X4 ◇ X5) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq11
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq12
  have eq93 (X0 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X5) ◇ X3)) ◇ X0) = X3 := superpose eq52 eq73
  have eq97 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := superpose eq81 eq7
  have eq107 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X2 := superpose eq97 eq67
  have eq110 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X0 := superpose eq107 eq60
  have eq111 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq110 eq93
  have eq130 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq111 eq17
  have eq135 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq111 eq130
  have eq137 (X0 X1 : G) : X0 = X1 := superpose eq111 eq135
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq137 eq8
  subsumption eq139 eq137


@[equational_result]
theorem Equation5809_implies_Equation2 (G : Type*) [Magma G] (h : Equation5809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq12 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation5810_implies_Equation2 (G : Type*) [Magma G] (h : Equation5810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := superpose eq11 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq13 eq11
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq13
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq12
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation5811_implies_Equation2 (G : Type*) [Magma G] (h : Equation5811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq10
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation5814_implies_Equation2 (G : Type*) [Magma G] (h : Equation5814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq21 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation5817_implies_Equation2 (G : Type*) [Magma G] (h : Equation5817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation5819_implies_Equation2 (G : Type*) [Magma G] (h : Equation5819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2)))) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2)))) ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X0)) ◇ X1))) = X0 := superpose eq9 eq10
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = (X0 ◇ X0) := superpose eq7 eq13
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq13 eq13
  have eq41 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq30 eq7
  have eq49 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose eq33 eq23
  have eq55 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq33 eq49
  have eq56 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq41 eq55
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq41 eq56
  have eq64 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq57 eq13
  have eq76 (X0 X1 : G) : X0 = X1 := superpose eq57 eq64
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq81 eq76


@[equational_result]
theorem Equation5821_implies_Equation2 (G : Type*) [Magma G] (h : Equation5821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq19 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq12 eq11
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq19 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation5824_implies_Equation2 (G : Type*) [Magma G] (h : Equation5824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation5827_implies_Equation2 (G : Type*) [Magma G] (h : Equation5827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation5829_implies_Equation2 (G : Type*) [Magma G] (h : Equation5829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq13 eq13
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq13 eq17
  have eq37 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq27 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq58 eq50


@[equational_result]
theorem Equation5831_implies_Equation2 (G : Type*) [Magma G] (h : Equation5831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq17 eq9
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq31 eq25


@[equational_result]
theorem Equation5835_implies_Equation2 (G : Type*) [Magma G] (h : Equation5835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq12 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation5839_implies_Equation2 (G : Type*) [Magma G] (h : Equation5839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq34 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq20 eq7
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq45 eq39


@[equational_result]
theorem Equation5841_implies_Equation2 (G : Type*) [Magma G] (h : Equation5841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X2 ◇ ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X1))) = X2 := superpose eq10 eq9
  have eq19 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ (X3 ◇ ((X2 ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ X2))) = X3 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2)))) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2))))) = X0 := superpose eq7 eq9
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose eq13 eq17
  have eq64 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq22 eq10
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq22 eq7
  have eq73 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq22 eq10
  have eq80 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ (X3 ◇ ((X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ X2))) = X3 := superpose eq64 eq19
  have eq144 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq69 eq69
  have eq146 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) := superpose eq9 eq69
  have eq147 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))))) := superpose eq80 eq69
  have eq164 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) = X0 := superpose eq144 eq36
  have eq186 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := superpose eq144 eq164
  have eq204 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq146 eq147
  have eq205 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq73 eq204
  have eq209 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := superpose eq205 eq186
  have eq215 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq205 eq209
  have eq273 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq144
  have eq305 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq144 eq273
  have eq307 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := superpose eq305 eq22
  have eq319 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq305 eq215
  have eq355 (X0 X3 : G) : X0 = X3 := superpose eq307 eq319
  have eq424 (X0 : G) : sK0 ≠ X0 := superpose eq355 eq8
  subsumption eq424 eq355


@[equational_result]
theorem Equation5842_implies_Equation2 (G : Type*) [Magma G] (h : Equation5842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X2 := superpose eq10 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := superpose eq7 eq9
  have eq79 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq7
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) = X2 := superpose eq79 eq9
  have eq91 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq79 eq18
  have eq113 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq79 eq85
  have eq114 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq79 eq113
  have eq115 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq79 eq91
  have eq116 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq79 eq115
  have eq117 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq79 eq116
  have eq118 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq79 eq117
  have eq119 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq118 eq114
  have eq126 (X0 X2 : G) : X0 = X2 := superpose eq119 eq119
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq8
  subsumption eq134 eq126


@[equational_result]
theorem Equation5843_implies_Equation2 (G : Type*) [Magma G] (h : Equation5843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq24 eq7
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq46 eq38


@[equational_result]
theorem Equation5845_implies_Equation2 (G : Type*) [Magma G] (h : Equation5845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) = (X0 ◇ X0) := superpose eq9 eq11
  have eq27 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq31 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X1 := superpose eq15 eq27
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X0) := superpose eq31 eq26
  have eq35 (X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ X3) := superpose eq31 eq11
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq32 eq7
  have eq50 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq35 eq37
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq15 eq50
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq52 eq52
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq95 eq53


@[equational_result]
theorem Equation5846_implies_Equation2 (G : Type*) [Magma G] (h : Equation5846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq14 eq12
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq57 eq33


@[equational_result]
theorem Equation5847_implies_Equation2 (G : Type*) [Magma G] (h : Equation5847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X3)) = (X0 ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq11 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := superpose eq11 eq7
  have eq29 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq21 eq25
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq134 eq56


@[equational_result]
theorem Equation5848_implies_Equation2 (G : Type*) [Magma G] (h : Equation5848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5850_implies_Equation2 (G : Type*) [Magma G] (h : Equation5850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq10
  have eq17 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq13 eq9
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq15 eq16
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq15 eq17
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := superpose eq15 eq13
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq18
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq22
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq26 eq21
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq23 eq27
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq35 eq30


@[equational_result]
theorem Equation5851_implies_Equation2 (G : Type*) [Magma G] (h : Equation5851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) = (X1 ◇ ((X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0)) := superpose eq7 eq11
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3)))) = X2 := superpose eq12 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq15 eq11
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3))) = X2 := superpose eq20 eq18
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X3)) = X2 := superpose eq20 eq21
  have eq27 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq20 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq33 eq28


@[equational_result]
theorem Equation5852_implies_Equation2 (G : Type*) [Magma G] (h : Equation5852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5854_implies_Equation2 (G : Type*) [Magma G] (h : Equation5854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X3) = X2 := superpose eq16 eq9
  have eq22 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq16 eq17
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq10 eq22
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq32 eq23


@[equational_result]
theorem Equation5856_implies_Equation2 (G : Type*) [Magma G] (h : Equation5856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ (X2 ◇ (X4 ◇ (X0 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) = X2 := superpose eq10 eq9
  have eq15 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq10 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation5859_implies_Equation2 (G : Type*) [Magma G] (h : Equation5859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation5860_implies_Equation2 (G : Type*) [Magma G] (h : Equation5860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5862_implies_Equation2 (G : Type*) [Magma G] (h : Equation5862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X4 := superpose eq7 eq12
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation5863_implies_Equation2 (G : Type*) [Magma G] (h : Equation5863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq12 eq9
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation5864_implies_Equation2 (G : Type*) [Magma G] (h : Equation5864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X4 ◇ ((X0 ◇ X5) ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5865_implies_Equation2 (G : Type*) [Magma G] (h : Equation5865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5867_implies_Equation2 (G : Type*) [Magma G] (h : Equation5867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose eq7 eq10
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq14 eq12
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq14 eq11
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq14 eq17
  have eq21 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq20 eq16
  have eq22 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq21 eq10
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation5869_implies_Equation2 (G : Type*) [Magma G] (h : Equation5869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5871_implies_Equation2 (G : Type*) [Magma G] (h : Equation5871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq28 eq12


@[equational_result]
theorem Equation5873_implies_Equation2 (G : Type*) [Magma G] (h : Equation5873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5875_implies_Equation2 (G : Type*) [Magma G] (h : Equation5875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X1))) ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2))))) = X2 := superpose eq7 eq9
  have eq81 (X0 X1 : G) : X0 = X1 := superpose eq7 eq17
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq90 eq81


@[equational_result]
theorem Equation5876_implies_Equation2 (G : Type*) [Magma G] (h : Equation5876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0))) = X1 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)))) = X1 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) ◇ (((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) ◇ (X3 ◇ ((((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) ◇ X3) ◇ X3)))) = X2 := superpose eq9 eq12
  have eq102 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq17
  have eq115 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq102 eq7
  have eq116 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq102 eq9
  have eq124 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ ((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X3)))) = X2 := superpose eq102 eq18
  have eq188 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq115 eq116
  have eq189 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) = X2 := superpose eq188 eq124
  have eq190 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq115 eq189
  have eq192 (X0 X2 : G) : X0 = X2 := superpose eq115 eq190
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq207 eq192


@[equational_result]
theorem Equation5877_implies_Equation2 (G : Type*) [Magma G] (h : Equation5877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5879_implies_Equation2 (G : Type*) [Magma G] (h : Equation5879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5880_implies_Equation2 (G : Type*) [Magma G] (h : Equation5880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq22 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq14 eq9
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation5881_implies_Equation2 (G : Type*) [Magma G] (h : Equation5881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation5882_implies_Equation2 (G : Type*) [Magma G] (h : Equation5882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5885_implies_Equation2 (G : Type*) [Magma G] (h : Equation5885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) ◇ (X4 ◇ (X0 ◇ X4))) ◇ (X0 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3)))))) = X2 := superpose eq7 eq10
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq24 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation5886_implies_Equation2 (G : Type*) [Magma G] (h : Equation5886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5890_implies_Equation2 (G : Type*) [Magma G] (h : Equation5890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X4 ◇ (X2 ◇ (X0 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X2) = X4 := superpose eq10 eq9
  have eq15 (X1 X2 X4 : G) : (X1 ◇ X2) = X4 := superpose eq10 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation5893_implies_Equation2 (G : Type*) [Magma G] (h : Equation5893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq11
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq65 eq22


@[equational_result]
theorem Equation5894_implies_Equation2 (G : Type*) [Magma G] (h : Equation5894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5896_implies_Equation2 (G : Type*) [Magma G] (h : Equation5896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq9
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq17 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation5897_implies_Equation2 (G : Type*) [Magma G] (h : Equation5897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq14 eq26
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq50 eq27


@[equational_result]
theorem Equation5898_implies_Equation2 (G : Type*) [Magma G] (h : Equation5898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X4 ◇ ((X4 ◇ X5) ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5899_implies_Equation2 (G : Type*) [Magma G] (h : Equation5899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5901_implies_Equation2 (G : Type*) [Magma G] (h : Equation5901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq12
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation5902_implies_Equation2 (G : Type*) [Magma G] (h : Equation5902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5903_implies_Equation2 (G : Type*) [Magma G] (h : Equation5903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5904_implies_Equation2 (G : Type*) [Magma G] (h : Equation5904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5906_implies_Equation2 (G : Type*) [Magma G] (h : Equation5906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation5907_implies_Equation2 (G : Type*) [Magma G] (h : Equation5907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ X1)) ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) = (X1 ◇ (X0 ◇ (X5 ◇ X1))) := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X4 ◇ (X5 ◇ X1)) ◇ X3))) = X2 := superpose eq17 eq10
  have eq23 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq17 eq21
  have eq25 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = (X0 ◇ (X4 ◇ X2)) := superpose eq23 eq12
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq23 eq7
  have eq29 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X0 := superpose eq27 eq25
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq27
  have eq37 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq31 eq23
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq31 eq37
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq46 eq41


@[equational_result]
theorem Equation5908_implies_Equation2 (G : Type*) [Magma G] (h : Equation5908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation5909_implies_Equation2 (G : Type*) [Magma G] (h : Equation5909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X5 ◇ (X6 ◇ (X0 ◇ X7)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X6) = X5 := superpose eq10 eq9
  have eq15 (X1 X5 X6 : G) : (X1 ◇ X6) = X5 := superpose eq10 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation5911_implies_Equation2 (G : Type*) [Magma G] (h : Equation5911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq12 eq12
  have eq16 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq12 eq12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq16 eq7
  have eq26 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq16 eq14
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq22 eq26
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq59 eq33


@[equational_result]
theorem Equation5912_implies_Equation2 (G : Type*) [Magma G] (h : Equation5912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq57 eq14


@[equational_result]
theorem Equation5913_implies_Equation2 (G : Type*) [Magma G] (h : Equation5913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5914_implies_Equation2 (G : Type*) [Magma G] (h : Equation5914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5916_implies_Equation2 (G : Type*) [Magma G] (h : Equation5916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation5917_implies_Equation2 (G : Type*) [Magma G] (h : Equation5917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq21 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq13 eq9
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation5918_implies_Equation2 (G : Type*) [Magma G] (h : Equation5918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X4 ◇ ((X5 ◇ X5) ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5919_implies_Equation2 (G : Type*) [Magma G] (h : Equation5919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5921_implies_Equation2 (G : Type*) [Magma G] (h : Equation5921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation5922_implies_Equation2 (G : Type*) [Magma G] (h : Equation5922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation5923_implies_Equation2 (G : Type*) [Magma G] (h : Equation5923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5924_implies_Equation2 (G : Type*) [Magma G] (h : Equation5924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X5 ◇ ((X6 ◇ X7) ◇ X7))))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5925_implies_Equation2 (G : Type*) [Magma G] (h : Equation5925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X9 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X9)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation5928_implies_Equation2 (G : Type*) [Magma G] (h : Equation5928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq9
  have eq28 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq19 eq9
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation5931_implies_Equation2 (G : Type*) [Magma G] (h : Equation5931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq17 eq14
  have eq35 (X0 X1 : G) : X0 = X1 := superpose eq17 eq26
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation5933_implies_Equation2 (G : Type*) [Magma G] (h : Equation5933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2)))) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq9 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X4 ◇ X0))) = X4 := superpose eq10 eq9
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq14
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) := superpose eq14 eq10
  have eq56 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X4 ◇ X0))) = X4 := superpose eq37 eq31
  have eq68 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq14 eq42
  have eq71 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (X4 ◇ X0))) = X4 := superpose eq68 eq56
  have eq86 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) = X4 := superpose eq68 eq71
  have eq87 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq68 eq86
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq87 eq87
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq90 eq88


@[equational_result]
theorem Equation5935_implies_Equation2 (G : Type*) [Magma G] (h : Equation5935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq25 eq14


@[equational_result]
theorem Equation5938_implies_Equation2 (G : Type*) [Magma G] (h : Equation5938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq26 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq17 eq14
  have eq35 (X0 X1 : G) : X0 = X1 := superpose eq17 eq26
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation5941_implies_Equation2 (G : Type*) [Magma G] (h : Equation5941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq9
  have eq26 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq17 eq7
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq17 eq26
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation5943_implies_Equation2 (G : Type*) [Magma G] (h : Equation5943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq13
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq19 eq19
  have eq59 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq26 eq7
  have eq72 (X0 X1 : G) : X0 = X1 := superpose eq9 eq59
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq82 eq72


@[equational_result]
theorem Equation5945_implies_Equation2 (G : Type*) [Magma G] (h : Equation5945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq12 eq11
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq13 eq10
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq13 eq14
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation5949_implies_Equation2 (G : Type*) [Magma G] (h : Equation5949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq62 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq67 eq62


@[equational_result]
theorem Equation5953_implies_Equation2 (G : Type*) [Magma G] (h : Equation5953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq31 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq21 eq11
  have eq32 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq21 eq10
  have eq45 (X0 X1 : G) : X0 = X1 := superpose eq31 eq32
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq50 eq45


@[equational_result]
theorem Equation5956_implies_Equation2 (G : Type*) [Magma G] (h : Equation5956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))))) = X2 := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X2 := superpose eq10 eq16
  have eq23 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq10 eq22
  have eq24 (X0 X2 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := superpose eq23 eq9
  have eq28 (X0 X1 : G) : ((X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X1 := superpose eq10 eq24
  have eq40 (X0 X1 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq10 eq28
  have eq41 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq10 eq40
  have eq43 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq41 eq10
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq41 eq43
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq41 eq47
  have eq49 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq48 eq23
  have eq54 (X0 X1 : G) : X0 = X1 := superpose eq48 eq49
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq62 eq54


@[equational_result]
theorem Equation5957_implies_Equation2 (G : Type*) [Magma G] (h : Equation5957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq38 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq9
  have eq60 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq75 eq60


@[equational_result]
theorem Equation5959_implies_Equation2 (G : Type*) [Magma G] (h : Equation5959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq9 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1))) ◇ X2) = ((X5 ◇ (X0 ◇ X1)) ◇ ((X5 ◇ (X0 ◇ X1)) ◇ X5)) := superpose eq11 eq11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq9 eq11
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1))) ◇ X2) = X1 := superpose eq15 eq27
  have eq52 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq36 eq7
  have eq57 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X2 := superpose eq52 eq29
  have eq60 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq57 eq7
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq60 eq60
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq73 eq71


@[equational_result]
theorem Equation5960_implies_Equation2 (G : Type*) [Magma G] (h : Equation5960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X2 ◇ X3)) ◇ X4) := superpose eq16 eq10
  have eq27 (X0 X1 X4 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X4) := superpose eq16 eq22
  have eq28 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq16 eq27
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq16 eq28
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq39 eq37


@[equational_result]
theorem Equation5961_implies_Equation2 (G : Type*) [Magma G] (h : Equation5961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5962_implies_Equation2 (G : Type*) [Magma G] (h : Equation5962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq12 eq10
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation5965_implies_Equation2 (G : Type*) [Magma G] (h : Equation5965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq11 eq11
  have eq15 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = X2 := superpose eq14 eq9
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq11 eq15
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation5968_implies_Equation2 (G : Type*) [Magma G] (h : Equation5968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation5970_implies_Equation2 (G : Type*) [Magma G] (h : Equation5970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation5972_implies_Equation2 (G : Type*) [Magma G] (h : Equation5972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq30 eq22


@[equational_result]
theorem Equation5975_implies_Equation2 (G : Type*) [Magma G] (h : Equation5975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq71 eq17


@[equational_result]
theorem Equation5977_implies_Equation2 (G : Type*) [Magma G] (h : Equation5977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation5978_implies_Equation2 (G : Type*) [Magma G] (h : Equation5978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5980_implies_Equation2 (G : Type*) [Magma G] (h : Equation5980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5981_implies_Equation2 (G : Type*) [Magma G] (h : Equation5981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5982_implies_Equation2 (G : Type*) [Magma G] (h : Equation5982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5984_implies_Equation2 (G : Type*) [Magma G] (h : Equation5984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := superpose eq7 eq9
  have eq55 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X5 ◇ (X5 ◇ (X5 ◇ ((((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X0)))) ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X0)))) ◇ X4)) ◇ X5)))) := superpose eq10 eq9
  have eq77 (X0 X1 X4 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X5 ◇ X4) := superpose eq22 eq55
  have eq86 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = (X4 ◇ X5) := superpose eq77 eq77
  have eq146 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq86
  have eq262 (X0 X3 : G) : X0 = X3 := superpose eq7 eq146
  have eq396 (X0 : G) : sK0 ≠ X0 := superpose eq262 eq8
  subsumption eq396 eq262


@[equational_result]
theorem Equation5986_implies_Equation2 (G : Type*) [Magma G] (h : Equation5986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation5988_implies_Equation2 (G : Type*) [Magma G] (h : Equation5988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5989_implies_Equation2 (G : Type*) [Magma G] (h : Equation5989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5990_implies_Equation2 (G : Type*) [Magma G] (h : Equation5990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5992_implies_Equation2 (G : Type*) [Magma G] (h : Equation5992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5993_implies_Equation2 (G : Type*) [Magma G] (h : Equation5993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation5994_implies_Equation2 (G : Type*) [Magma G] (h : Equation5994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation5996_implies_Equation2 (G : Type*) [Magma G] (h : Equation5996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5997_implies_Equation2 (G : Type*) [Magma G] (h : Equation5997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5998_implies_Equation2 (G : Type*) [Magma G] (h : Equation5998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation5999_implies_Equation2 (G : Type*) [Magma G] (h : Equation5999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6001_implies_Equation2 (G : Type*) [Magma G] (h : Equation6001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) = X2 := superpose eq11 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))) = X1 := superpose eq11 eq9
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq15
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := superpose eq23 eq7
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X3 ◇ X0))) = X1 := superpose eq23 eq16
  have eq30 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X1 := superpose eq28 eq29
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq62 eq36


@[equational_result]
theorem Equation6003_implies_Equation2 (G : Type*) [Magma G] (h : Equation6003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation6005_implies_Equation2 (G : Type*) [Magma G] (h : Equation6005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))))))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ X0)))))) := superpose eq12 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) = (((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq7 eq18
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2))))) := superpose eq23 eq7
  have eq75 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) ◇ X0)) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X0)) := superpose eq9 eq50
  have eq85 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) := superpose eq7 eq75
  have eq106 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))))))) = X0 := superpose eq85 eq9
  have eq107 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq85 eq7
  have eq108 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0))))) := superpose eq85 eq7
  have eq114 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (X2 ◇ ((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)))) = (((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (X2 ◇ ((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (X2 ◇ ((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X3 ◇ (((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (X2 ◇ ((((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))))))) := superpose eq85 eq18
  have eq117 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq107
  have eq118 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq117 eq106
  have eq122 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq117 eq85
  have eq123 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq117 eq108
  have eq129 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = (((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) ◇ (X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0))))) := superpose eq117 eq114
  have eq163 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq122 eq7
  have eq182 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X0))) = X0 := superpose eq163 eq118
  have eq270 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq122 eq182
  have eq271 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq163 eq182
  have eq316 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq270 eq117
  have eq318 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq270 eq123
  have eq324 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ (((X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) := superpose eq270 eq129
  have eq438 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))))) := superpose eq270 eq324
  have eq439 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) := superpose eq316 eq438
  have eq440 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq318 eq439
  have eq732 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq271 eq440
  have eq1134 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq271 eq7
  have eq1156 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq732 eq1134
  have eq1200 (X0 X2 : G) : X0 = X2 := superpose eq1156 eq1156
  have eq1360 (X0 : G) : sK0 ≠ X0 := superpose eq1200 eq8
  subsumption eq1360 eq1200


@[equational_result]
theorem Equation6007_implies_Equation2 (G : Type*) [Magma G] (h : Equation6007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6011_implies_Equation2 (G : Type*) [Magma G] (h : Equation6011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation6013_implies_Equation2 (G : Type*) [Magma G] (h : Equation6013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation6014_implies_Equation2 (G : Type*) [Magma G] (h : Equation6014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation6015_implies_Equation2 (G : Type*) [Magma G] (h : Equation6015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation6016_implies_Equation2 (G : Type*) [Magma G] (h : Equation6016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6018_implies_Equation2 (G : Type*) [Magma G] (h : Equation6018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X2 := superpose eq22 eq22
  have eq66 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq123 eq66


@[equational_result]
theorem Equation6020_implies_Equation2 (G : Type*) [Magma G] (h : Equation6020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6022_implies_Equation2 (G : Type*) [Magma G] (h : Equation6022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6023_implies_Equation2 (G : Type*) [Magma G] (h : Equation6023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6024_implies_Equation2 (G : Type*) [Magma G] (h : Equation6024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6026_implies_Equation2 (G : Type*) [Magma G] (h : Equation6026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6027_implies_Equation2 (G : Type*) [Magma G] (h : Equation6027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6028_implies_Equation2 (G : Type*) [Magma G] (h : Equation6028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6030_implies_Equation2 (G : Type*) [Magma G] (h : Equation6030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6031_implies_Equation2 (G : Type*) [Magma G] (h : Equation6031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6032_implies_Equation2 (G : Type*) [Magma G] (h : Equation6032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6033_implies_Equation2 (G : Type*) [Magma G] (h : Equation6033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6036_implies_Equation2 (G : Type*) [Magma G] (h : Equation6036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3))) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ ((X4 ◇ (X3 ◇ X2)) ◇ X4))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X2 := superpose eq23 eq22
  have eq57 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq29 eq9
  have eq62 (X0 X1 X2 X4 : G) : (X0 ◇ X2) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) := superpose eq57 eq18
  have eq72 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq23 eq62
  have eq127 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) = X2 := superpose eq72 eq7
  have eq302 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq127 eq23
  have eq320 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq302 eq9
  have eq455 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := superpose eq29 eq320
  have eq507 (X0 X3 : G) : X0 = X3 := superpose eq455 eq455
  have eq611 (X0 : G) : sK0 ≠ X0 := superpose eq507 eq8
  subsumption eq611 eq507


@[equational_result]
theorem Equation6037_implies_Equation2 (G : Type*) [Magma G] (h : Equation6037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation6039_implies_Equation2 (G : Type*) [Magma G] (h : Equation6039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6040_implies_Equation2 (G : Type*) [Magma G] (h : Equation6040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6041_implies_Equation2 (G : Type*) [Magma G] (h : Equation6041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6043_implies_Equation2 (G : Type*) [Magma G] (h : Equation6043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6044_implies_Equation2 (G : Type*) [Magma G] (h : Equation6044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6045_implies_Equation2 (G : Type*) [Magma G] (h : Equation6045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6047_implies_Equation2 (G : Type*) [Magma G] (h : Equation6047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6048_implies_Equation2 (G : Type*) [Magma G] (h : Equation6048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6049_implies_Equation2 (G : Type*) [Magma G] (h : Equation6049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6050_implies_Equation2 (G : Type*) [Magma G] (h : Equation6050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6052_implies_Equation2 (G : Type*) [Magma G] (h : Equation6052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ ((X5 ◇ X0) ◇ X3))) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ (X1 ◇ X2)))) ◇ (X5 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X0)) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) = ((X5 ◇ ((X6 ◇ X0) ◇ X4)) ◇ ((X5 ◇ ((X6 ◇ X0) ◇ X4)) ◇ X0)) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X1))) = X0 := superpose eq7 eq9
  have eq66 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X6 ◇ (X6 ◇ (X7 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X0)) ◇ X6)))) = (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X3) ◇ (X5 ◇ X0)) := superpose eq11 eq9
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X0)) = (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X3) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X3) ◇ (X5 ◇ X0))) := superpose eq11 eq7
  have eq76 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X0) = (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X3) ◇ (X5 ◇ X0)) := superpose eq7 eq66
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X0)) = (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X3) ◇ (X4 ◇ X0)) := superpose eq76 eq67
  have eq78 (X0 X2 X3 X4 : G) : (X4 ◇ X0) = ((X2 ◇ X3) ◇ (X4 ◇ X0)) := superpose eq76 eq77
  have eq79 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ (X1 ◇ X2)))) ◇ (X5 ◇ X0)) = X2 := superpose eq78 eq10
  have eq97 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X5 ◇ X0)) = X2 := superpose eq78 eq79
  have eq98 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X0)) = X2 := superpose eq78 eq97
  have eq99 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) = X4 := superpose eq98 eq25
  have eq100 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq99 eq7
  have eq109 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := superpose eq100 eq29
  have eq131 (X0 X1 X3 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X1)) = X0 := superpose eq100 eq109
  have eq132 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq100 eq131
  have eq139 (X0 X1 : G) : X0 = X1 := superpose eq100 eq132
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq139 eq8
  subsumption eq144 eq139


@[equational_result]
theorem Equation6053_implies_Equation2 (G : Type*) [Magma G] (h : Equation6053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 X5 : G) : (X5 ◇ (X5 ◇ X2)) = X0 := superpose eq7 eq11
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X1)) ◇ X5) = (X4 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq11
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X4) = X0 := superpose eq7 eq11
  have eq39 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq55 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq39 eq20
  have eq59 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X0 := superpose eq55 eq22
  have eq68 (X1 X4 : G) : (X4 ◇ X1) = X1 := superpose eq59 eq55
  have eq72 (X0 X2 X5 : G) : (X5 ◇ X2) = X0 := superpose eq68 eq17
  have eq79 (X0 X3 : G) : X0 = X3 := superpose eq72 eq72
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq84 eq79


@[equational_result]
theorem Equation6054_implies_Equation2 (G : Type*) [Magma G] (h : Equation6054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation6055_implies_Equation2 (G : Type*) [Magma G] (h : Equation6055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6057_implies_Equation2 (G : Type*) [Magma G] (h : Equation6057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6058_implies_Equation2 (G : Type*) [Magma G] (h : Equation6058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6059_implies_Equation2 (G : Type*) [Magma G] (h : Equation6059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6060_implies_Equation2 (G : Type*) [Magma G] (h : Equation6060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6062_implies_Equation2 (G : Type*) [Magma G] (h : Equation6062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6063_implies_Equation2 (G : Type*) [Magma G] (h : Equation6063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6064_implies_Equation2 (G : Type*) [Magma G] (h : Equation6064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6065_implies_Equation2 (G : Type*) [Magma G] (h : Equation6065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6067_implies_Equation2 (G : Type*) [Magma G] (h : Equation6067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6068_implies_Equation2 (G : Type*) [Magma G] (h : Equation6068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6069_implies_Equation2 (G : Type*) [Magma G] (h : Equation6069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6070_implies_Equation2 (G : Type*) [Magma G] (h : Equation6070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6072_implies_Equation2 (G : Type*) [Magma G] (h : Equation6072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6073_implies_Equation2 (G : Type*) [Magma G] (h : Equation6073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6074_implies_Equation2 (G : Type*) [Magma G] (h : Equation6074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6075_implies_Equation2 (G : Type*) [Magma G] (h : Equation6075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6076_implies_Equation2 (G : Type*) [Magma G] (h : Equation6076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6078_implies_Equation2 (G : Type*) [Magma G] (h : Equation6078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq98 eq24


@[equational_result]
theorem Equation6079_implies_Equation2 (G : Type*) [Magma G] (h : Equation6079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq12 eq11
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq15 eq13
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq39 eq24


@[equational_result]
theorem Equation6080_implies_Equation2 (G : Type*) [Magma G] (h : Equation6080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq26 eq19


@[equational_result]
theorem Equation6082_implies_Equation2 (G : Type*) [Magma G] (h : Equation6082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq101 eq38


@[equational_result]
theorem Equation6084_implies_Equation2 (G : Type*) [Magma G] (h : Equation6084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation6087_implies_Equation2 (G : Type*) [Magma G] (h : Equation6087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq55 eq27


@[equational_result]
theorem Equation6088_implies_Equation2 (G : Type*) [Magma G] (h : Equation6088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq15 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq14 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq15 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6090_implies_Equation2 (G : Type*) [Magma G] (h : Equation6090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq37
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq105 eq42


@[equational_result]
theorem Equation6091_implies_Equation2 (G : Type*) [Magma G] (h : Equation6091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq12 eq9
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq13 eq12
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation6092_implies_Equation2 (G : Type*) [Magma G] (h : Equation6092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X5) ◇ X5))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq7
  have eq14 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq13 eq12
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6093_implies_Equation2 (G : Type*) [Magma G] (h : Equation6093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation6095_implies_Equation2 (G : Type*) [Magma G] (h : Equation6095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq128 eq40


@[equational_result]
theorem Equation6097_implies_Equation2 (G : Type*) [Magma G] (h : Equation6097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation6099_implies_Equation2 (G : Type*) [Magma G] (h : Equation6099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation6101_implies_Equation2 (G : Type*) [Magma G] (h : Equation6101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6104_implies_Equation2 (G : Type*) [Magma G] (h : Equation6104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))))) ◇ (X4 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))))))))) ◇ (X5 ◇ (X4 ◇ (((X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))))) ◇ (X4 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))))))))))))) = X5 := superpose eq9 eq9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ X1))))) = X3 := superpose eq12 eq9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) = (X0 ◇ (X0 ◇ X1)) := superpose eq12 eq7
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq22 eq7
  have eq44 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))))) = X3 := superpose eq22 eq7
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq22 eq12
  have eq57 (X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) = X1 := superpose eq7 eq49
  have eq58 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq57 eq12
  have eq62 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))) = X3 := superpose eq57 eq21
  have eq63 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq57 eq22
  have eq79 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq63 eq39
  have eq82 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))))) = X3 := superpose eq63 eq44
  have eq92 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))) = X3 := superpose eq63 eq82
  have eq110 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = (X1 ◇ X0) := superpose eq58 eq9
  have eq116 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((((X1 ◇ X3) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3))))))) ◇ (X5 ◇ (X4 ◇ (((X1 ◇ X3) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3))))))))))) = X5 := superpose eq110 eq11
  have eq135 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))) ◇ (X3 ◇ (X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))))))) = X3 := superpose eq79 eq116
  have eq140 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2))))))) := superpose eq58 eq116
  have eq145 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X3)) = X3 := superpose eq140 eq135
  have eq153 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))) = X3 := superpose eq145 eq92
  have eq159 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = X3 := superpose eq110 eq153
  have eq161 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1))) = X3 := superpose eq159 eq62
  have eq174 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq159 eq161
  have eq175 (X0 X1 : G) : X0 = X1 := superpose eq79 eq174
  have eq186 (X0 : G) : sK0 ≠ X0 := superpose eq175 eq8
  subsumption eq186 eq175


@[equational_result]
theorem Equation6105_implies_Equation2 (G : Type*) [Magma G] (h : Equation6105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6107_implies_Equation2 (G : Type*) [Magma G] (h : Equation6107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq7 eq7
  have eq31 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq10 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq31
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq121 eq36


@[equational_result]
theorem Equation6108_implies_Equation2 (G : Type*) [Magma G] (h : Equation6108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq130 eq41


@[equational_result]
theorem Equation6109_implies_Equation2 (G : Type*) [Magma G] (h : Equation6109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation6110_implies_Equation2 (G : Type*) [Magma G] (h : Equation6110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation6113_implies_Equation2 (G : Type*) [Magma G] (h : Equation6113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq143 eq54


@[equational_result]
theorem Equation6114_implies_Equation2 (G : Type*) [Magma G] (h : Equation6114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6118_implies_Equation2 (G : Type*) [Magma G] (h : Equation6118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq10 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation6121_implies_Equation2 (G : Type*) [Magma G] (h : Equation6121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq36 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq12
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq121 eq50


@[equational_result]
theorem Equation6122_implies_Equation2 (G : Type*) [Magma G] (h : Equation6122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6124_implies_Equation2 (G : Type*) [Magma G] (h : Equation6124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq7 eq9
  have eq23 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X4 := superpose eq17 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq49 eq32


@[equational_result]
theorem Equation6125_implies_Equation2 (G : Type*) [Magma G] (h : Equation6125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X0 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation6126_implies_Equation2 (G : Type*) [Magma G] (h : Equation6126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq12 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6127_implies_Equation2 (G : Type*) [Magma G] (h : Equation6127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation6129_implies_Equation2 (G : Type*) [Magma G] (h : Equation6129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq11 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq130 eq40


@[equational_result]
theorem Equation6130_implies_Equation2 (G : Type*) [Magma G] (h : Equation6130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X2))) ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X3 ◇ X0) ◇ X2) ◇ (X4 ◇ X0))) = X4 := superpose eq12 eq10
  have eq17 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq12 eq13
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation6131_implies_Equation2 (G : Type*) [Magma G] (h : Equation6131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq13 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation6132_implies_Equation2 (G : Type*) [Magma G] (h : Equation6132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6134_implies_Equation2 (G : Type*) [Magma G] (h : Equation6134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq51 eq33


@[equational_result]
theorem Equation6135_implies_Equation2 (G : Type*) [Magma G] (h : Equation6135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X4 := superpose eq11 eq11
  have eq61 (X0 X5 : G) : X0 = X5 := superpose eq11 eq17
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq160 eq61


@[equational_result]
theorem Equation6136_implies_Equation2 (G : Type*) [Magma G] (h : Equation6136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq63 eq15


@[equational_result]
theorem Equation6137_implies_Equation2 (G : Type*) [Magma G] (h : Equation6137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq10 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation6139_implies_Equation2 (G : Type*) [Magma G] (h : Equation6139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X4))) ◇ (X5 ◇ (X0 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq12 eq12
  have eq22 (X0 X1 X4 X5 : G) : (X1 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X1)))) = X5 := superpose eq15 eq9
  have eq25 (X1 X5 : G) : (X1 ◇ X1) = X5 := superpose eq15 eq22
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq12 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation6140_implies_Equation2 (G : Type*) [Magma G] (h : Equation6140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6141_implies_Equation2 (G : Type*) [Magma G] (h : Equation6141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X0 := superpose eq10 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6142_implies_Equation2 (G : Type*) [Magma G] (h : Equation6142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X0 := superpose eq10 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6144_implies_Equation2 (G : Type*) [Magma G] (h : Equation6144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation6145_implies_Equation2 (G : Type*) [Magma G] (h : Equation6145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation6146_implies_Equation2 (G : Type*) [Magma G] (h : Equation6146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X0 ◇ ((X5 ◇ X5) ◇ X5))))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X0 := superpose eq13 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6147_implies_Equation2 (G : Type*) [Magma G] (h : Equation6147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X7)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation6149_implies_Equation2 (G : Type*) [Magma G] (h : Equation6149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) = X5 := superpose eq7 eq7
  have eq35 (X0 X7 : G) : X0 = X7 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation6150_implies_Equation2 (G : Type*) [Magma G] (h : Equation6150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (X2 ◇ (X0 ◇ X1)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation6151_implies_Equation2 (G : Type*) [Magma G] (h : Equation6151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation6152_implies_Equation2 (G : Type*) [Magma G] (h : Equation6152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X5 ◇ (X0 ◇ ((X6 ◇ X7) ◇ X7))))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X4)) = X0 := superpose eq13 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6153_implies_Equation2 (G : Type*) [Magma G] (h : Equation6153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X9 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X9)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation6155_implies_Equation2 (G : Type*) [Magma G] (h : Equation6155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq77 eq28


@[equational_result]
theorem Equation6157_implies_Equation2 (G : Type*) [Magma G] (h : Equation6157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation6159_implies_Equation2 (G : Type*) [Magma G] (h : Equation6159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) = ((X1 ◇ ((X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3)))))) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3)))))) ◇ (X3 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3)))))))))) := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) = X0 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = ((X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) ◇ X0) := superpose eq7 eq12
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ X0))) = X2 := superpose eq14 eq7
  have eq30 (X0 X1 X3 : G) : ((X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) ◇ (X3 ◇ ((X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) ◇ X1))) = X1 := superpose eq14 eq12
  have eq38 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = ((X0 ◇ ((((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))))) ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))))) ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((((X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))))) ◇ X0) ◇ X0)))))) := superpose eq14 eq10
  have eq52 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose eq29 eq14
  have eq67 (X0 X1 X3 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (X3 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ X1))) = X1 := superpose eq52 eq30
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) = (X2 ◇ X2) := superpose eq7 eq52
  have eq104 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq52 eq29
  have eq134 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = ((X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)))))) := superpose eq96 eq38
  have eq168 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = ((X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X0)) ◇ X2))) := superpose eq104 eq134
  have eq169 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = X2 := superpose eq67 eq168
  have eq170 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq169 eq7
  have eq227 (X0 X2 : G) : X0 = X2 := superpose eq170 eq170
  have eq245 (X0 : G) : sK0 ≠ X0 := superpose eq227 eq8
  subsumption eq245 eq227


@[equational_result]
theorem Equation6161_implies_Equation2 (G : Type*) [Magma G] (h : Equation6161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6165_implies_Equation2 (G : Type*) [Magma G] (h : Equation6165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation6167_implies_Equation2 (G : Type*) [Magma G] (h : Equation6167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation6168_implies_Equation2 (G : Type*) [Magma G] (h : Equation6168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq63 eq44


@[equational_result]
theorem Equation6169_implies_Equation2 (G : Type*) [Magma G] (h : Equation6169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation6170_implies_Equation2 (G : Type*) [Magma G] (h : Equation6170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6172_implies_Equation2 (G : Type*) [Magma G] (h : Equation6172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X5 ◇ (X1 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)))) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = (X0 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)))) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := superpose eq7 eq9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X2 := superpose eq22 eq21
  have eq35 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq22
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1))) := superpose eq9 eq22
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0))) := superpose eq9 eq22
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = ((X2 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq22 eq22
  have eq39 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) = X4 := superpose eq9 eq22
  have eq52 (X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X5 ◇ (X1 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)))) := superpose eq36 eq11
  have eq74 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) = ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq14 eq14
  have eq105 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) = X0 := superpose eq14 eq30
  have eq107 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0))) := superpose eq14 eq22
  have eq125 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) := superpose eq35 eq74
  have eq135 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq107 eq37
  have eq143 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)))) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq135 eq20
  have eq152 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) = X4 := superpose eq135 eq39
  have eq160 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq135 eq125
  have eq162 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := superpose eq135 eq22
  have eq183 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq135 eq143
  have eq184 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq38 eq183
  have eq185 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq135 eq184
  have eq186 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq38 eq185
  have eq187 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq135 eq186
  have eq188 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq135 eq187
  have eq189 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq135 eq188
  have eq193 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := superpose eq135 eq162
  have eq194 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = X2 := superpose eq193 eq189
  have eq197 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X2 := superpose eq194 eq160
  have eq199 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq197 eq105
  have eq200 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq199 eq38
  have eq203 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq200 eq30
  have eq205 (X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X5 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq200 eq52
  have eq215 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X2)))) = X4 := superpose eq200 eq152
  have eq231 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq200 eq205
  have eq232 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq203 eq231
  have eq249 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) = X4 := superpose eq232 eq215
  have eq250 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq232 eq249
  have eq251 (X0 X3 : G) : X0 = X3 := superpose eq250 eq250
  have eq259 (X0 : G) : sK0 ≠ X0 := superpose eq251 eq8
  subsumption eq259 eq251


@[equational_result]
theorem Equation6174_implies_Equation2 (G : Type*) [Magma G] (h : Equation6174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6176_implies_Equation2 (G : Type*) [Magma G] (h : Equation6176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6177_implies_Equation2 (G : Type*) [Magma G] (h : Equation6177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6178_implies_Equation2 (G : Type*) [Magma G] (h : Equation6178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6180_implies_Equation2 (G : Type*) [Magma G] (h : Equation6180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6181_implies_Equation2 (G : Type*) [Magma G] (h : Equation6181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6182_implies_Equation2 (G : Type*) [Magma G] (h : Equation6182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6184_implies_Equation2 (G : Type*) [Magma G] (h : Equation6184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6185_implies_Equation2 (G : Type*) [Magma G] (h : Equation6185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6186_implies_Equation2 (G : Type*) [Magma G] (h : Equation6186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6187_implies_Equation2 (G : Type*) [Magma G] (h : Equation6187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6189_implies_Equation2 (G : Type*) [Magma G] (h : Equation6189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) ◇ (X2 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X4))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X2 := superpose eq23 eq22
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq10 eq31
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq162 eq97


@[equational_result]
theorem Equation6190_implies_Equation2 (G : Type*) [Magma G] (h : Equation6190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X3))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X4 ◇ X2) ◇ X4)) = (X3 ◇ (X4 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X4)))) := superpose eq9 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) = X2 := superpose eq24 eq23
  have eq38 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X3))) := superpose eq9 eq24
  have eq39 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3))) := superpose eq9 eq24
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq24 eq24
  have eq46 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X4 ◇ (X2 ◇ (X4 ◇ ((X3 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) ◇ X2)))) := superpose eq24 eq9
  have eq57 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X4 ◇ (X2 ◇ (X4 ◇ ((X3 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X2)))) := superpose eq40 eq46
  have eq68 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))))) := superpose eq9 eq32
  have eq78 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X2) := superpose eq7 eq68
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq78 eq7
  have eq93 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X4)))) = (X1 ◇ (X4 ◇ X2)) := superpose eq78 eq28
  have eq95 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := superpose eq78 eq38
  have eq96 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3))) := superpose eq78 eq39
  have eq117 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq93 eq57
  have eq139 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X3 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := superpose eq117 eq96
  have eq140 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = (X3 ◇ X2) := superpose eq139 eq95
  have eq141 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq140 eq79
  have eq157 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq140 eq141
  have eq196 (X0 X3 : G) : X0 = X3 := superpose eq157 eq157
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq196 eq8
  subsumption eq199 eq196


@[equational_result]
theorem Equation6191_implies_Equation2 (G : Type*) [Magma G] (h : Equation6191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation6193_implies_Equation2 (G : Type*) [Magma G] (h : Equation6193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6194_implies_Equation2 (G : Type*) [Magma G] (h : Equation6194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6195_implies_Equation2 (G : Type*) [Magma G] (h : Equation6195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6197_implies_Equation2 (G : Type*) [Magma G] (h : Equation6197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6198_implies_Equation2 (G : Type*) [Magma G] (h : Equation6198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6199_implies_Equation2 (G : Type*) [Magma G] (h : Equation6199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6201_implies_Equation2 (G : Type*) [Magma G] (h : Equation6201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6202_implies_Equation2 (G : Type*) [Magma G] (h : Equation6202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6203_implies_Equation2 (G : Type*) [Magma G] (h : Equation6203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6204_implies_Equation2 (G : Type*) [Magma G] (h : Equation6204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6206_implies_Equation2 (G : Type*) [Magma G] (h : Equation6206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq7
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq158 eq63


@[equational_result]
theorem Equation6207_implies_Equation2 (G : Type*) [Magma G] (h : Equation6207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6208_implies_Equation2 (G : Type*) [Magma G] (h : Equation6208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation6209_implies_Equation2 (G : Type*) [Magma G] (h : Equation6209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6211_implies_Equation2 (G : Type*) [Magma G] (h : Equation6211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6212_implies_Equation2 (G : Type*) [Magma G] (h : Equation6212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6213_implies_Equation2 (G : Type*) [Magma G] (h : Equation6213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6214_implies_Equation2 (G : Type*) [Magma G] (h : Equation6214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6216_implies_Equation2 (G : Type*) [Magma G] (h : Equation6216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6217_implies_Equation2 (G : Type*) [Magma G] (h : Equation6217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6218_implies_Equation2 (G : Type*) [Magma G] (h : Equation6218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6219_implies_Equation2 (G : Type*) [Magma G] (h : Equation6219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6221_implies_Equation2 (G : Type*) [Magma G] (h : Equation6221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6222_implies_Equation2 (G : Type*) [Magma G] (h : Equation6222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6223_implies_Equation2 (G : Type*) [Magma G] (h : Equation6223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6224_implies_Equation2 (G : Type*) [Magma G] (h : Equation6224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6226_implies_Equation2 (G : Type*) [Magma G] (h : Equation6226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6227_implies_Equation2 (G : Type*) [Magma G] (h : Equation6227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6228_implies_Equation2 (G : Type*) [Magma G] (h : Equation6228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6229_implies_Equation2 (G : Type*) [Magma G] (h : Equation6229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6230_implies_Equation2 (G : Type*) [Magma G] (h : Equation6230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6233_implies_Equation2 (G : Type*) [Magma G] (h : Equation6233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3))))) = X2 := superpose eq7 eq11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq12
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq20
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq162 eq50


@[equational_result]
theorem Equation6234_implies_Equation2 (G : Type*) [Magma G] (h : Equation6234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6237_implies_Equation2 (G : Type*) [Magma G] (h : Equation6237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X3))) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X4 ◇ (X4 ◇ (X2 ◇ X4)))) := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X3)) = (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ (X4 ◇ (X4 ◇ (X3 ◇ X4)))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1))) ◇ X0)) ◇ (X4 ◇ (X4 ◇ (X2 ◇ X4)))) = X3 := superpose eq7 eq9
  have eq56 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1))) = X0 := superpose eq9 eq11
  have eq143 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X1))) ◇ X0) = X3 := superpose eq56 eq9
  have eq606 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) ◇ (X3 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X2) = X4 := superpose eq11 eq143
  have eq650 (X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X2) = X4 := superpose eq56 eq606
  have eq791 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ X1) := superpose eq56 eq650
  have eq1051 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq791 eq56
  have eq1211 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0)) = X2 := superpose eq13 eq14
  have eq1255 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq56 eq1211
  have eq1267 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X2 ◇ X1) ◇ X2) ◇ X0) ◇ X1) := superpose eq143 eq1211
  have eq1817 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) ◇ X2) = X0 := superpose eq1211 eq1255
  have eq2742 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) := superpose eq1267 eq1267
  have eq3233 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq2742 eq1211
  have eq3785 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq1051 eq1817
  have eq3787 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq3785 eq3233
  have eq3809 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq650 eq3787
  have eq3860 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq3809 eq7
  have eq5949 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X2) ◇ X1) := superpose eq3860 eq1255
  have eq5950 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq3860 eq2742
  have eq5964 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq5949 eq1211
  have eq5975 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq3860 eq5950
  have eq5982 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq5975 eq5964
  have eq5990 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq5982 eq3860
  have eq6009 (X0 X2 : G) : X0 = X2 := superpose eq5990 eq5990
  have eq6011 (X0 : G) : sK0 ≠ X0 := superpose eq6009 eq8
  subsumption eq6011 eq6009


@[equational_result]
theorem Equation6238_implies_Equation2 (G : Type*) [Magma G] (h : Equation6238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6241_implies_Equation2 (G : Type*) [Magma G] (h : Equation6241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq9
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq34 eq24


@[equational_result]
theorem Equation6242_implies_Equation2 (G : Type*) [Magma G] (h : Equation6242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation6244_implies_Equation2 (G : Type*) [Magma G] (h : Equation6244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation6245_implies_Equation2 (G : Type*) [Magma G] (h : Equation6245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation6246_implies_Equation2 (G : Type*) [Magma G] (h : Equation6246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation6247_implies_Equation2 (G : Type*) [Magma G] (h : Equation6247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6249_implies_Equation2 (G : Type*) [Magma G] (h : Equation6249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X5 ◇ (X5 ◇ ((X4 ◇ (X4 ◇ (X2 ◇ X1))) ◇ X1)))) = (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X4 ◇ (X4 ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0))))) = X2 := superpose eq24 eq23
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq24
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1))) = (X1 ◇ (X2 ◇ X1)) := superpose eq9 eq24
  have eq55 (X1 X2 X4 X5 : G) : (X1 ◇ (X5 ◇ (X5 ◇ ((X4 ◇ (X4 ◇ (X2 ◇ X1))) ◇ X1)))) = (X1 ◇ (X2 ◇ X1)) := superpose eq40 eq11
  have eq129 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X0))) := superpose eq14 eq24
  have eq184 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) = ((X4 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (((X4 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X4) ◇ (X4 ◇ ((X0 ◇ X2) ◇ X0)))) := superpose eq9 eq39
  have eq187 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = ((X3 ◇ (X1 ◇ X0)) ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq39 eq39
  have eq232 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X2) = (X2 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2)))) := superpose eq39 eq7
  have eq246 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X2)) := superpose eq55 eq232
  have eq247 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq246 eq7
  have eq277 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) = ((X4 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (((X4 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X4) ◇ (X4 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq246 eq184
  have eq278 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X3 ◇ (X1 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq246 eq187
  have eq301 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))) := superpose eq246 eq129
  have eq303 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := superpose eq246 eq24
  have eq333 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) = ((X4 ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq246 eq277
  have eq334 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X3 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X0))))) := superpose eq246 eq278
  have eq349 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := superpose eq246 eq303
  have eq350 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X0))))) = X1 := superpose eq349 eq334
  have eq352 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) = X0 := superpose eq350 eq333
  have eq394 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq14 eq247
  have eq409 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq34 eq394
  have eq410 (X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X1 ◇ X2)) := superpose eq409 eq246
  have eq412 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X0 := superpose eq410 eq247
  have eq429 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))) := superpose eq410 eq301
  have eq469 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq410 eq429
  have eq470 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq352 eq469
  have eq485 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X0 := superpose eq470 eq412
  have eq516 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq470 eq485
  have eq517 (X0 X3 : G) : X0 = X3 := superpose eq516 eq516
  have eq519 (X0 : G) : sK0 ≠ X0 := superpose eq517 eq8
  subsumption eq519 eq517


@[equational_result]
theorem Equation6250_implies_Equation2 (G : Type*) [Magma G] (h : Equation6250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X3))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X3) ◇ X0))))) = X2 := superpose eq9 eq7
  have eq37 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq7 eq29
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq37
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq144 eq58


@[equational_result]
theorem Equation6251_implies_Equation2 (G : Type*) [Magma G] (h : Equation6251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6253_implies_Equation2 (G : Type*) [Magma G] (h : Equation6253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6254_implies_Equation2 (G : Type*) [Magma G] (h : Equation6254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6255_implies_Equation2 (G : Type*) [Magma G] (h : Equation6255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6257_implies_Equation2 (G : Type*) [Magma G] (h : Equation6257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6258_implies_Equation2 (G : Type*) [Magma G] (h : Equation6258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6259_implies_Equation2 (G : Type*) [Magma G] (h : Equation6259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6261_implies_Equation2 (G : Type*) [Magma G] (h : Equation6261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6262_implies_Equation2 (G : Type*) [Magma G] (h : Equation6262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6263_implies_Equation2 (G : Type*) [Magma G] (h : Equation6263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6264_implies_Equation2 (G : Type*) [Magma G] (h : Equation6264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6267_implies_Equation2 (G : Type*) [Magma G] (h : Equation6267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ ((X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq73 eq52


@[equational_result]
theorem Equation6268_implies_Equation2 (G : Type*) [Magma G] (h : Equation6268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation6270_implies_Equation2 (G : Type*) [Magma G] (h : Equation6270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6271_implies_Equation2 (G : Type*) [Magma G] (h : Equation6271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6272_implies_Equation2 (G : Type*) [Magma G] (h : Equation6272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6274_implies_Equation2 (G : Type*) [Magma G] (h : Equation6274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6275_implies_Equation2 (G : Type*) [Magma G] (h : Equation6275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6276_implies_Equation2 (G : Type*) [Magma G] (h : Equation6276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6278_implies_Equation2 (G : Type*) [Magma G] (h : Equation6278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6279_implies_Equation2 (G : Type*) [Magma G] (h : Equation6279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6280_implies_Equation2 (G : Type*) [Magma G] (h : Equation6280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6281_implies_Equation2 (G : Type*) [Magma G] (h : Equation6281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6283_implies_Equation2 (G : Type*) [Magma G] (h : Equation6283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ ((X3 ◇ X4) ◇ X1)) ◇ (X5 ◇ X0)) ◇ X0)) = X4 := superpose eq12 eq7
  have eq23 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq14 eq21
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq160 eq47


@[equational_result]
theorem Equation6284_implies_Equation2 (G : Type*) [Magma G] (h : Equation6284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ (X2 ◇ X3))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 X6 : G) : (X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X5 ◇ (X5 ◇ ((X6 ◇ X0) ◇ X5))))) = X3 := superpose eq7 eq11
  have eq25 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq12
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq182 eq63


@[equational_result]
theorem Equation6285_implies_Equation2 (G : Type*) [Magma G] (h : Equation6285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation6286_implies_Equation2 (G : Type*) [Magma G] (h : Equation6286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6288_implies_Equation2 (G : Type*) [Magma G] (h : Equation6288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6289_implies_Equation2 (G : Type*) [Magma G] (h : Equation6289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6290_implies_Equation2 (G : Type*) [Magma G] (h : Equation6290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6291_implies_Equation2 (G : Type*) [Magma G] (h : Equation6291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6293_implies_Equation2 (G : Type*) [Magma G] (h : Equation6293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6294_implies_Equation2 (G : Type*) [Magma G] (h : Equation6294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6295_implies_Equation2 (G : Type*) [Magma G] (h : Equation6295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6296_implies_Equation2 (G : Type*) [Magma G] (h : Equation6296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6298_implies_Equation2 (G : Type*) [Magma G] (h : Equation6298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6299_implies_Equation2 (G : Type*) [Magma G] (h : Equation6299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6300_implies_Equation2 (G : Type*) [Magma G] (h : Equation6300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6301_implies_Equation2 (G : Type*) [Magma G] (h : Equation6301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6303_implies_Equation2 (G : Type*) [Magma G] (h : Equation6303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6304_implies_Equation2 (G : Type*) [Magma G] (h : Equation6304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6305_implies_Equation2 (G : Type*) [Magma G] (h : Equation6305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6306_implies_Equation2 (G : Type*) [Magma G] (h : Equation6306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6307_implies_Equation2 (G : Type*) [Magma G] (h : Equation6307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6309_implies_Equation2 (G : Type*) [Magma G] (h : Equation6309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq60 eq16


@[equational_result]
theorem Equation6310_implies_Equation2 (G : Type*) [Magma G] (h : Equation6310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation6311_implies_Equation2 (G : Type*) [Magma G] (h : Equation6311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6312_implies_Equation2 (G : Type*) [Magma G] (h : Equation6312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6314_implies_Equation2 (G : Type*) [Magma G] (h : Equation6314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq66 eq17


@[equational_result]
theorem Equation6315_implies_Equation2 (G : Type*) [Magma G] (h : Equation6315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X1))) ◇ X0)) = X4 := superpose eq7 eq7
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq7
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq154 eq52


@[equational_result]
theorem Equation6316_implies_Equation2 (G : Type*) [Magma G] (h : Equation6316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation6317_implies_Equation2 (G : Type*) [Magma G] (h : Equation6317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6319_implies_Equation2 (G : Type*) [Magma G] (h : Equation6319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation6320_implies_Equation2 (G : Type*) [Magma G] (h : Equation6320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation6321_implies_Equation2 (G : Type*) [Magma G] (h : Equation6321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation6322_implies_Equation2 (G : Type*) [Magma G] (h : Equation6322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6324_implies_Equation2 (G : Type*) [Magma G] (h : Equation6324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X0)) = X4 := superpose eq7 eq7
  have eq37 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq57 eq37


@[equational_result]
theorem Equation6325_implies_Equation2 (G : Type*) [Magma G] (h : Equation6325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation6326_implies_Equation2 (G : Type*) [Magma G] (h : Equation6326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation6327_implies_Equation2 (G : Type*) [Magma G] (h : Equation6327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6329_implies_Equation2 (G : Type*) [Magma G] (h : Equation6329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation6330_implies_Equation2 (G : Type*) [Magma G] (h : Equation6330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation6331_implies_Equation2 (G : Type*) [Magma G] (h : Equation6331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6332_implies_Equation2 (G : Type*) [Magma G] (h : Equation6332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation6333_implies_Equation2 (G : Type*) [Magma G] (h : Equation6333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6335_implies_Equation2 (G : Type*) [Magma G] (h : Equation6335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation6336_implies_Equation2 (G : Type*) [Magma G] (h : Equation6336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X4))) ◇ X0)) = X4 := superpose eq7 eq7
  have eq21 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq11 eq7
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq181 eq72


@[equational_result]
theorem Equation6337_implies_Equation2 (G : Type*) [Magma G] (h : Equation6337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq75 eq12


@[equational_result]
theorem Equation6338_implies_Equation2 (G : Type*) [Magma G] (h : Equation6338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6340_implies_Equation2 (G : Type*) [Magma G] (h : Equation6340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6341_implies_Equation2 (G : Type*) [Magma G] (h : Equation6341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6342_implies_Equation2 (G : Type*) [Magma G] (h : Equation6342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6343_implies_Equation2 (G : Type*) [Magma G] (h : Equation6343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6345_implies_Equation2 (G : Type*) [Magma G] (h : Equation6345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6346_implies_Equation2 (G : Type*) [Magma G] (h : Equation6346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6347_implies_Equation2 (G : Type*) [Magma G] (h : Equation6347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6348_implies_Equation2 (G : Type*) [Magma G] (h : Equation6348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6350_implies_Equation2 (G : Type*) [Magma G] (h : Equation6350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6351_implies_Equation2 (G : Type*) [Magma G] (h : Equation6351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6352_implies_Equation2 (G : Type*) [Magma G] (h : Equation6352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6353_implies_Equation2 (G : Type*) [Magma G] (h : Equation6353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6355_implies_Equation2 (G : Type*) [Magma G] (h : Equation6355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6356_implies_Equation2 (G : Type*) [Magma G] (h : Equation6356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6357_implies_Equation2 (G : Type*) [Magma G] (h : Equation6357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6358_implies_Equation2 (G : Type*) [Magma G] (h : Equation6358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6359_implies_Equation2 (G : Type*) [Magma G] (h : Equation6359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6361_implies_Equation2 (G : Type*) [Magma G] (h : Equation6361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation6362_implies_Equation2 (G : Type*) [Magma G] (h : Equation6362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq69 eq12


@[equational_result]
theorem Equation6363_implies_Equation2 (G : Type*) [Magma G] (h : Equation6363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation6364_implies_Equation2 (G : Type*) [Magma G] (h : Equation6364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6366_implies_Equation2 (G : Type*) [Magma G] (h : Equation6366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6367_implies_Equation2 (G : Type*) [Magma G] (h : Equation6367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6368_implies_Equation2 (G : Type*) [Magma G] (h : Equation6368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6369_implies_Equation2 (G : Type*) [Magma G] (h : Equation6369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6371_implies_Equation2 (G : Type*) [Magma G] (h : Equation6371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6372_implies_Equation2 (G : Type*) [Magma G] (h : Equation6372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6373_implies_Equation2 (G : Type*) [Magma G] (h : Equation6373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6374_implies_Equation2 (G : Type*) [Magma G] (h : Equation6374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6376_implies_Equation2 (G : Type*) [Magma G] (h : Equation6376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6377_implies_Equation2 (G : Type*) [Magma G] (h : Equation6377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6378_implies_Equation2 (G : Type*) [Magma G] (h : Equation6378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6379_implies_Equation2 (G : Type*) [Magma G] (h : Equation6379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6381_implies_Equation2 (G : Type*) [Magma G] (h : Equation6381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6382_implies_Equation2 (G : Type*) [Magma G] (h : Equation6382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6383_implies_Equation2 (G : Type*) [Magma G] (h : Equation6383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6384_implies_Equation2 (G : Type*) [Magma G] (h : Equation6384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6385_implies_Equation2 (G : Type*) [Magma G] (h : Equation6385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6387_implies_Equation2 (G : Type*) [Magma G] (h : Equation6387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X0)) = X4 := superpose eq7 eq7
  have eq37 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq57 eq37


@[equational_result]
theorem Equation6388_implies_Equation2 (G : Type*) [Magma G] (h : Equation6388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation6389_implies_Equation2 (G : Type*) [Magma G] (h : Equation6389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation6390_implies_Equation2 (G : Type*) [Magma G] (h : Equation6390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6392_implies_Equation2 (G : Type*) [Magma G] (h : Equation6392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6393_implies_Equation2 (G : Type*) [Magma G] (h : Equation6393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6394_implies_Equation2 (G : Type*) [Magma G] (h : Equation6394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6395_implies_Equation2 (G : Type*) [Magma G] (h : Equation6395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6397_implies_Equation2 (G : Type*) [Magma G] (h : Equation6397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6398_implies_Equation2 (G : Type*) [Magma G] (h : Equation6398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6399_implies_Equation2 (G : Type*) [Magma G] (h : Equation6399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6400_implies_Equation2 (G : Type*) [Magma G] (h : Equation6400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6402_implies_Equation2 (G : Type*) [Magma G] (h : Equation6402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6403_implies_Equation2 (G : Type*) [Magma G] (h : Equation6403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6404_implies_Equation2 (G : Type*) [Magma G] (h : Equation6404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6405_implies_Equation2 (G : Type*) [Magma G] (h : Equation6405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6407_implies_Equation2 (G : Type*) [Magma G] (h : Equation6407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6408_implies_Equation2 (G : Type*) [Magma G] (h : Equation6408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6409_implies_Equation2 (G : Type*) [Magma G] (h : Equation6409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6410_implies_Equation2 (G : Type*) [Magma G] (h : Equation6410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6411_implies_Equation2 (G : Type*) [Magma G] (h : Equation6411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6413_implies_Equation2 (G : Type*) [Magma G] (h : Equation6413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation6414_implies_Equation2 (G : Type*) [Magma G] (h : Equation6414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation6415_implies_Equation2 (G : Type*) [Magma G] (h : Equation6415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6416_implies_Equation2 (G : Type*) [Magma G] (h : Equation6416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6417_implies_Equation2 (G : Type*) [Magma G] (h : Equation6417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6419_implies_Equation2 (G : Type*) [Magma G] (h : Equation6419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6420_implies_Equation2 (G : Type*) [Magma G] (h : Equation6420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6421_implies_Equation2 (G : Type*) [Magma G] (h : Equation6421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6422_implies_Equation2 (G : Type*) [Magma G] (h : Equation6422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6423_implies_Equation2 (G : Type*) [Magma G] (h : Equation6423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6425_implies_Equation2 (G : Type*) [Magma G] (h : Equation6425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6426_implies_Equation2 (G : Type*) [Magma G] (h : Equation6426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6427_implies_Equation2 (G : Type*) [Magma G] (h : Equation6427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6428_implies_Equation2 (G : Type*) [Magma G] (h : Equation6428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6429_implies_Equation2 (G : Type*) [Magma G] (h : Equation6429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6431_implies_Equation2 (G : Type*) [Magma G] (h : Equation6431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X3) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6432_implies_Equation2 (G : Type*) [Magma G] (h : Equation6432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X3) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6433_implies_Equation2 (G : Type*) [Magma G] (h : Equation6433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X3) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6434_implies_Equation2 (G : Type*) [Magma G] (h : Equation6434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X3) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6435_implies_Equation2 (G : Type*) [Magma G] (h : Equation6435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X3) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6437_implies_Equation2 (G : Type*) [Magma G] (h : Equation6437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X4) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6438_implies_Equation2 (G : Type*) [Magma G] (h : Equation6438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X4) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6439_implies_Equation2 (G : Type*) [Magma G] (h : Equation6439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X4) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6440_implies_Equation2 (G : Type*) [Magma G] (h : Equation6440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X4) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6441_implies_Equation2 (G : Type*) [Magma G] (h : Equation6441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X4) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6443_implies_Equation2 (G : Type*) [Magma G] (h : Equation6443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6444_implies_Equation2 (G : Type*) [Magma G] (h : Equation6444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6445_implies_Equation2 (G : Type*) [Magma G] (h : Equation6445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6446_implies_Equation2 (G : Type*) [Magma G] (h : Equation6446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6447_implies_Equation2 (G : Type*) [Magma G] (h : Equation6447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6448_implies_Equation2 (G : Type*) [Magma G] (h : Equation6448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X6)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6654_implies_Equation2 (G : Type*) [Magma G] (h : Equation6654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq22
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq11 eq45
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq106 eq54


@[equational_result]
theorem Equation6657_implies_Equation2 (G : Type*) [Magma G] (h : Equation6657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq13 eq18
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq44 eq40


@[equational_result]
theorem Equation6659_implies_Equation2 (G : Type*) [Magma G] (h : Equation6659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X3 ◇ ((X3 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq7
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq10
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq11
  have eq31 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq22
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq15
  have eq35 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq15 eq10
  have eq40 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq33
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq40 eq29
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ ((X3 ◇ X3) ◇ X0))) = X3 := superpose eq40 eq9
  have eq67 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq40 eq47
  have eq68 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq41 eq67
  have eq69 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq41 eq68
  have eq74 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq69 eq35
  have eq76 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq74 eq69
  have eq86 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq74 eq76
  have eq87 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq74 eq86
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq87 eq87
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq90 eq88


@[equational_result]
theorem Equation6660_implies_Equation2 (G : Type*) [Magma G] (h : Equation6660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation6661_implies_Equation2 (G : Type*) [Magma G] (h : Equation6661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation6664_implies_Equation2 (G : Type*) [Magma G] (h : Equation6664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X1 := superpose eq11 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq32 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq20 eq19
  have eq62 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq80 eq62


@[equational_result]
theorem Equation6667_implies_Equation2 (G : Type*) [Magma G] (h : Equation6667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq45 (X0 X1 : G) : X0 = X1 := superpose eq13 eq22
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq49 eq45


@[equational_result]
theorem Equation6669_implies_Equation2 (G : Type*) [Magma G] (h : Equation6669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq11 eq11
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))))) ◇ X0)) := superpose eq9 eq11
  have eq77 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (X0 ◇ X0)) := superpose eq24 eq24
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq24 eq11
  have eq88 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq24 eq14
  have eq89 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))))) ◇ (X0 ◇ X0)) := superpose eq7 eq77
  have eq127 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq87 eq7
  have eq185 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq24 eq88
  have eq196 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq88 eq24
  have eq210 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq7 eq185
  have eq212 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq210 eq89
  have eq214 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq87 eq196
  have eq474 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq127 eq11
  have eq708 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ X1)) := superpose eq474 eq26
  have eq743 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq708
  have eq744 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq743 eq11
  have eq848 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq743 eq210
  have eq849 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq743 eq212
  have eq879 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq744 eq214
  have eq958 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq743 eq849
  have eq959 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq958 eq879
  have eq1002 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq959 eq848
  have eq1027 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq743 eq1002
  have eq1029 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := superpose eq1027 eq7
  have eq1045 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1027 eq744
  have eq1083 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1027 eq1029
  have eq1200 (X0 X1 : G) : X0 = X1 := superpose eq1083 eq1045
  have eq1205 (X0 : G) : sK0 ≠ X0 := superpose eq1200 eq8
  subsumption eq1205 eq1200


@[equational_result]
theorem Equation6671_implies_Equation2 (G : Type*) [Magma G] (h : Equation6671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X0 ◇ (X4 ◇ X5)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) = X1 := superpose eq11 eq9
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq13
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq11 eq16
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq23 eq20


@[equational_result]
theorem Equation6673_implies_Equation2 (G : Type*) [Magma G] (h : Equation6673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq28 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq35 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq17 eq28
  have eq69 (X0 X1 : G) : X0 = X1 := superpose eq17 eq35
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq93 eq69


@[equational_result]
theorem Equation6674_implies_Equation2 (G : Type*) [Magma G] (h : Equation6674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq21 eq13


@[equational_result]
theorem Equation6675_implies_Equation2 (G : Type*) [Magma G] (h : Equation6675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq9
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq11 eq18
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation6677_implies_Equation2 (G : Type*) [Magma G] (h : Equation6677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq22 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq47 eq22


@[equational_result]
theorem Equation6679_implies_Equation2 (G : Type*) [Magma G] (h : Equation6679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq7
  have eq19 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X2 := superpose eq15 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq19
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq11 eq23
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq53 eq26


@[equational_result]
theorem Equation6682_implies_Equation2 (G : Type*) [Magma G] (h : Equation6682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X3))) ◇ (X0 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq22 eq14


@[equational_result]
theorem Equation6683_implies_Equation2 (G : Type*) [Magma G] (h : Equation6683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X4))) ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation6685_implies_Equation2 (G : Type*) [Magma G] (h : Equation6685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X4 ◇ ((X4 ◇ X5) ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq12 eq12
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)) = X4 := superpose eq14 eq10
  have eq23 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X5)) = X4 := superpose eq14 eq20
  have eq24 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq23 eq11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq24
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq12 eq27
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq60 eq30


@[equational_result]
theorem Equation6686_implies_Equation2 (G : Type*) [Magma G] (h : Equation6686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X5 ◇ (X0 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation6687_implies_Equation2 (G : Type*) [Magma G] (h : Equation6687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X5 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation6688_implies_Equation2 (G : Type*) [Magma G] (h : Equation6688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X6 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6691_implies_Equation2 (G : Type*) [Magma G] (h : Equation6691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq35 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq20 eq10
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq35 eq20
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq58 eq50


@[equational_result]
theorem Equation6694_implies_Equation2 (G : Type*) [Magma G] (h : Equation6694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq11 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq34 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq20 eq7
  have eq49 (X0 X1 : G) : X0 = X1 := superpose eq34 eq21
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq66 eq49


@[equational_result]
theorem Equation6696_implies_Equation2 (G : Type*) [Magma G] (h : Equation6696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X3 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq11 eq11
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq14 eq9
  have eq59 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq10 eq9
  have eq69 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq59 eq34
  have eq99 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq59 eq11
  have eq109 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq69 eq13
  have eq123 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq14 eq109
  have eq158 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq123 eq7
  have eq214 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq123 eq158
  have eq228 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X0)) ◇ (X3 ◇ (((X1 ◇ (((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X0)) ◇ X3) ◇ X1))) = X3 := superpose eq158 eq10
  have eq238 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq214
  have eq292 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq238 eq7
  have eq300 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq238 eq12
  have eq311 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq292 eq300
  have eq312 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq238 eq311
  have eq315 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq312 eq292
  have eq316 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq123 eq315
  have eq325 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq316 eq59
  have eq335 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq316 eq99
  have eq387 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq325 eq13
  have eq495 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq325 eq335
  have eq496 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq316 eq495
  have eq649 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq387 eq7
  have eq664 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq316 eq649
  have eq665 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq496 eq664
  have eq667 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) = X3 := superpose eq665 eq228
  have eq733 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) = X3 := superpose eq665 eq667
  have eq734 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq665 eq733
  have eq735 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq665 eq734
  have eq736 (X0 X3 : G) : X0 = X3 := superpose eq735 eq735
  have eq741 (X0 : G) : sK0 ≠ X0 := superpose eq736 eq8
  subsumption eq741 eq736


@[equational_result]
theorem Equation6698_implies_Equation2 (G : Type*) [Magma G] (h : Equation6698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq14 eq11
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq21 eq18


@[equational_result]
theorem Equation6701_implies_Equation2 (G : Type*) [Magma G] (h : Equation6701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq26 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq17 eq7
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq10 eq26
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation6704_implies_Equation2 (G : Type*) [Magma G] (h : Equation6704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq14
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq17 eq7
  have eq26 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq17 eq20
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq26 eq17
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq39 eq29


@[equational_result]
theorem Equation6706_implies_Equation2 (G : Type*) [Magma G] (h : Equation6706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq10 eq10
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X3 ◇ (((X1 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X1 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0))) ◇ X1))) = X3 := superpose eq10 eq9
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))) ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq10
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X3 ◇ (((X1 ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0)) ◇ (X1 ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0))) ◇ X1))) = X3 := superpose eq12 eq17
  have eq28 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1))) = X3 := superpose eq10 eq27
  have eq32 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq12
  have eq33 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq10 eq12
  have eq48 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := superpose eq12 eq9
  have eq49 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq7
  have eq60 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X3 ◇ X2) ◇ X1)) := superpose eq33 eq25
  have eq63 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq33 eq28
  have eq64 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq33 eq32
  have eq82 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := superpose eq12 eq48
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := superpose eq10 eq82
  have eq84 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := superpose eq10 eq83
  have eq85 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq60 eq49
  have eq87 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq85 eq11
  have eq92 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := superpose eq85 eq84
  have eq95 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq64 eq92
  have eq102 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq95 eq87
  have eq111 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq95 eq102
  have eq112 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq111 eq63
  have eq122 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X3 := superpose eq111 eq112
  have eq123 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq111 eq122
  have eq140 (X0 X1 : G) : X0 = X1 := superpose eq111 eq123
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq140 eq8
  subsumption eq154 eq140


@[equational_result]
theorem Equation6707_implies_Equation2 (G : Type*) [Magma G] (h : Equation6707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq35 eq12


@[equational_result]
theorem Equation6708_implies_Equation2 (G : Type*) [Magma G] (h : Equation6708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq18 eq15


@[equational_result]
theorem Equation6710_implies_Equation2 (G : Type*) [Magma G] (h : Equation6710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq7 eq15
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq9 eq15
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0)))) = (X0 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ X1)) := superpose eq10 eq15
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq9
  have eq42 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq31 eq7
  have eq44 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X0))) = X1 := superpose eq31 eq11
  have eq52 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) := superpose eq32 eq33
  have eq53 (X0 X1 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) = X1 := superpose eq42 eq52
  have eq68 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq41 eq44
  have eq70 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq68 eq53
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq15 eq70
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq107 eq73


@[equational_result]
theorem Equation6712_implies_Equation2 (G : Type*) [Magma G] (h : Equation6712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq9
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq11 eq30
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq54 eq32


@[equational_result]
theorem Equation6714_implies_Equation2 (G : Type*) [Magma G] (h : Equation6714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq13
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq30 eq19


@[equational_result]
theorem Equation6715_implies_Equation2 (G : Type*) [Magma G] (h : Equation6715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq11 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation6716_implies_Equation2 (G : Type*) [Magma G] (h : Equation6716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq19 eq9
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq11 eq33
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq59 eq36


@[equational_result]
theorem Equation6720_implies_Equation2 (G : Type*) [Magma G] (h : Equation6720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = X2 := superpose eq11 eq10
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq11 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation6722_implies_Equation2 (G : Type*) [Magma G] (h : Equation6722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X5 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq29 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq16 eq29
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq47 eq30


@[equational_result]
theorem Equation6723_implies_Equation2 (G : Type*) [Magma G] (h : Equation6723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation6724_implies_Equation2 (G : Type*) [Magma G] (h : Equation6724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation6725_implies_Equation2 (G : Type*) [Magma G] (h : Equation6725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X6 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6727_implies_Equation2 (G : Type*) [Magma G] (h : Equation6727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq11
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq11 eq7
  have eq19 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3))) ◇ (X3 ◇ ((X4 ◇ X3) ◇ (X0 ◇ X0)))) = X3 := superpose eq11 eq10
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq11 eq10
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq11 eq10
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1)))) := superpose eq10 eq7
  have eq42 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq17 eq7
  have eq69 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = ((X0 ◇ ((X3 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq10 eq9
  have eq111 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq42 eq10
  have eq112 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq42 eq7
  have eq143 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq112 eq11
  have eq155 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq112 eq13
  have eq159 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq112 eq155
  have eq181 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq11 eq19
  have eq217 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) := superpose eq143 eq7
  have eq221 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq143 eq10
  have eq247 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq143 eq26
  have eq266 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq17 eq26
  have eq285 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) ◇ X0) := superpose eq111 eq247
  have eq292 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq13 eq266
  have eq293 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq112 eq292
  have eq294 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq112 eq293
  have eq307 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = ((((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))))) := superpose eq17 eq111
  have eq360 (X0 X1 X4 : G) : (X1 ◇ X0) = (X4 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X4)))) := superpose eq7 eq32
  have eq378 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq13 eq32
  have eq407 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose eq112 eq378
  have eq427 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq159 eq10
  have eq439 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq159 eq17
  have eq447 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq159 eq439
  have eq516 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) ◇ X0)) := superpose eq143 eq69
  have eq524 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq159 eq69
  have eq552 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = (((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq285 eq516
  have eq553 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq294 eq524
  have eq557 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq112 eq360
  have eq559 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := superpose eq7 eq360
  have eq666 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq26 eq28
  have eq711 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq112 eq559
  have eq732 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq559
  have eq733 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq559 eq559
  have eq737 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq559
  have eq748 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq559
  have eq808 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq711 eq181
  have eq819 (X0 X1 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := superpose eq732 eq666
  have eq832 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose eq737 eq552
  have eq833 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq737 eq553
  have eq834 (X0 X1 X3 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq832 eq221
  have eq835 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq832 eq217
  have eq836 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq833 eq427
  have eq852 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq748 eq808
  have eq866 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq852 eq836
  have eq869 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq711 eq866
  have eq870 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq869 eq13
  have eq880 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose eq869 eq407
  have eq881 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq869 eq447
  have eq902 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ X0)) := superpose eq870 eq880
  have eq903 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq112 eq902
  have eq911 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq881 eq835
  have eq937 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq911 eq834
  have eq949 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq903 eq937
  have eq1001 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq949 eq307
  have eq1036 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq949 eq733
  have eq1041 (X0 X1 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq949 eq819
  have eq1117 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq949 eq1001
  have eq1126 (X0 X1 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq1036 eq1041
  have eq1127 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq949 eq1126
  have eq1128 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq1036 eq1127
  have eq1129 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq1036 eq1128
  have eq1131 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq1129 eq1117
  have eq1133 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq1036 eq1131
  have eq1134 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq1036 eq1133
  have eq1135 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1134 eq557
  have eq1157 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq1135 eq7
  have eq1279 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq1135 eq1157
  have eq1280 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq1135 eq1279
  have eq1281 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1135 eq1280
  have eq2015 (X0 X2 : G) : X0 = X2 := superpose eq1281 eq1281
  have eq2017 (X0 : G) : sK0 ≠ X0 := superpose eq2015 eq8
  subsumption eq2017 eq2015


@[equational_result]
theorem Equation6728_implies_Equation2 (G : Type*) [Magma G] (h : Equation6728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3))) ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq13 eq10
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq38 eq20


@[equational_result]
theorem Equation6729_implies_Equation2 (G : Type*) [Magma G] (h : Equation6729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq38 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X2 := superpose eq22 eq10
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq38 eq22
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq97 eq59


@[equational_result]
theorem Equation6731_implies_Equation2 (G : Type*) [Magma G] (h : Equation6731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = (X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq9 eq9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq9 eq9
  have eq16 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq7 eq12
  have eq18 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq9 eq16
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq16
  have eq21 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq7
  have eq24 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq18
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0))) := superpose eq21 eq13
  have eq27 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq21 eq24
  have eq28 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq27
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := superpose eq28 eq7
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq28 eq16
  have eq45 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ X0)) := superpose eq28 eq26
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) := superpose eq28 eq45
  have eq56 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq29 eq29
  have eq70 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq56 eq56
  have eq78 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq28 eq70
  have eq80 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq78 eq46
  have eq83 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq80 eq29
  have eq96 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq83 eq33
  have eq110 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq83 eq96
  have eq127 (X0 X2 : G) : X0 = X2 := superpose eq110 eq110
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq135 eq127


@[equational_result]
theorem Equation6733_implies_Equation2 (G : Type*) [Magma G] (h : Equation6733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq38 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X2 := superpose eq22 eq10
  have eq49 (X0 X1 : G) : X0 = X1 := superpose eq11 eq38
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq53 eq49


@[equational_result]
theorem Equation6736_implies_Equation2 (G : Type*) [Magma G] (h : Equation6736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((((X0 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X4))) ◇ X2) ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))))) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq21 eq7
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq24 eq21
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq47 eq40


@[equational_result]
theorem Equation6737_implies_Equation2 (G : Type*) [Magma G] (h : Equation6737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq13 eq11
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq21 eq18


@[equational_result]
theorem Equation6739_implies_Equation2 (G : Type*) [Magma G] (h : Equation6739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X4 ◇ ((X5 ◇ X4) ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq12 eq11
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X0) = X4 := superpose eq36 eq10
  have eq74 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X0) = X4 := superpose eq36 eq60
  have eq95 (X0 X3 : G) : X0 = X3 := superpose eq12 eq74
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq110 eq95


@[equational_result]
theorem Equation6740_implies_Equation2 (G : Type*) [Magma G] (h : Equation6740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation6741_implies_Equation2 (G : Type*) [Magma G] (h : Equation6741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation6742_implies_Equation2 (G : Type*) [Magma G] (h : Equation6742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq22 eq19


@[equational_result]
theorem Equation6744_implies_Equation2 (G : Type*) [Magma G] (h : Equation6744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) := superpose eq15 eq15
  have eq114 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) ◇ (X0 ◇ X0)) := superpose eq15 eq32
  have eq134 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq114
  have eq172 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq134 eq7
  have eq173 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))))) = X1 := superpose eq134 eq9
  have eq178 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq134 eq15
  have eq310 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq178 eq7
  have eq316 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq178 eq15
  have eq347 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq310 eq316
  have eq349 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq347 eq172
  have eq350 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq347 eq173
  have eq397 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq349 eq347
  have eq512 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq349 eq7
  have eq552 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq512 eq397
  have eq553 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq552 eq15
  have eq610 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq552 eq350
  have eq814 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq552 eq7
  have eq894 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq814
  have eq941 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq552 eq894
  have eq1065 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq941 eq814
  have eq1090 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq941 eq1065
  have eq1091 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq552 eq1090
  have eq1223 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq553 eq1091
  have eq1315 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq1223 eq814
  have eq1330 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq1315 eq610
  have eq1338 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq552 eq1330
  have eq1348 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq1338 eq7
  have eq1534 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq1338 eq1348
  have eq1535 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq1338 eq1534
  have eq1536 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1338 eq1535
  have eq2281 (X0 X2 : G) : X0 = X2 := superpose eq1536 eq1536
  have eq2286 (X0 : G) : sK0 ≠ X0 := superpose eq2281 eq8
  subsumption eq2286 eq2281


@[equational_result]
theorem Equation6746_implies_Equation2 (G : Type*) [Magma G] (h : Equation6746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq35 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X2 := superpose eq20 eq10
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq11 eq35
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq47 eq40


@[equational_result]
theorem Equation6748_implies_Equation2 (G : Type*) [Magma G] (h : Equation6748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))))) = X2 := superpose eq10 eq7
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq13
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq10 eq35
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq57 eq57
  have eq186 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq186 eq90


@[equational_result]
theorem Equation6750_implies_Equation2 (G : Type*) [Magma G] (h : Equation6750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq41 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X2 := superpose eq22 eq10
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq53 eq45


@[equational_result]
theorem Equation6752_implies_Equation2 (G : Type*) [Magma G] (h : Equation6752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq9 eq9
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq28 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq28 eq26
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq34 eq10
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq37 eq34
  have eq48 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X3 := superpose eq47 eq18
  have eq54 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X3 := superpose eq47 eq48
  have eq55 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = X3 := superpose eq47 eq54
  have eq56 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq47 eq55
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq56 eq56
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq62 eq57


@[equational_result]
theorem Equation6754_implies_Equation2 (G : Type*) [Magma G] (h : Equation6754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq11 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq22 eq19


@[equational_result]
theorem Equation6756_implies_Equation2 (G : Type*) [Magma G] (h : Equation6756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ (X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))) ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) = X3 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0)))))) = X3 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ (X4 ◇ (X0 ◇ X0))) = X4 := superpose eq16 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq16 eq17
  have eq34 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X6 ◇ X5))) = (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq19 eq19
  have eq74 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq16 eq7
  have eq78 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X3 := superpose eq74 eq18
  have eq79 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X6 ◇ X5))) = X0 := superpose eq78 eq34
  have eq83 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq79 eq7
  have eq95 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := superpose eq83 eq20
  have eq111 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X3 := superpose eq83 eq95
  have eq112 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = X3 := superpose eq83 eq111
  have eq113 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq83 eq112
  have eq120 (X0 X1 : G) : X0 = X1 := superpose eq83 eq113
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq134 eq120


@[equational_result]
theorem Equation6757_implies_Equation2 (G : Type*) [Magma G] (h : Equation6757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq61 eq18


@[equational_result]
theorem Equation6758_implies_Equation2 (G : Type*) [Magma G] (h : Equation6758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation6759_implies_Equation2 (G : Type*) [Magma G] (h : Equation6759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq11 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq22 eq19


@[equational_result]
theorem Equation6762_implies_Equation2 (G : Type*) [Magma G] (h : Equation6762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq39 eq15


@[equational_result]
theorem Equation6763_implies_Equation2 (G : Type*) [Magma G] (h : Equation6763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq12
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq7 eq28
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq98 eq43


@[equational_result]
theorem Equation6765_implies_Equation2 (G : Type*) [Magma G] (h : Equation6765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq13
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq21 eq14


@[equational_result]
theorem Equation6767_implies_Equation2 (G : Type*) [Magma G] (h : Equation6767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq39 eq21


@[equational_result]
theorem Equation6770_implies_Equation2 (G : Type*) [Magma G] (h : Equation6770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq9 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6771_implies_Equation2 (G : Type*) [Magma G] (h : Equation6771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X2 := superpose eq11 eq10
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq11 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation6773_implies_Equation2 (G : Type*) [Magma G] (h : Equation6773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq14 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq11 eq23
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq33 eq29


