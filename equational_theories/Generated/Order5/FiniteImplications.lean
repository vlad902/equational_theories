import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Finite.Equation10218_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation10218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ X) ◇ Y) ◇ ((Z ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ ((Z ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ ((Z ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ X1)) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X0)) = X2 := superpose eq10 eq8
  have eq19 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ X3) = (X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq8
  have eq71 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2))) = ((X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2)) ◇ X0) := superpose eq18 eq14
  have eq87 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) := superpose eq8 eq17
  have eq97 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X2 := superpose eq17 eq18
  have eq210 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2)) = (((X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq18 eq87
  have eq251 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4) = ((((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4) ◇ (X2 ◇ X4)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ ((X5 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4) ◇ (X2 ◇ X4))) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4))) := superpose eq19 eq15
  have eq320 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4) := superpose eq10 eq251
  have eq324 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq320 eq18
  have eq327 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))) = ((X0 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq320 eq71
  have eq342 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq320 eq210
  have eq404 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq97 eq324
  have eq407 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq324 eq324
  have eq448 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq407 eq342
  have eq458 (X0 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq448 eq327
  have eq474 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (X0 ◇ X0) := superpose eq448 eq458
  have eq498 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq474 eq404
  have eq538 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq448 eq498
  have eq539 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq448 eq538
  have eq549 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq539 eq448
  have eq596 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq549 eq10
  have eq736 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = X0 := superpose eq549 eq596
  have eq737 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq549 eq736
  have eq738 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq549 eq737
  have eq739 (X0 X3 : G) : X0 = X3 := superpose eq738 eq738
  have eq741 (X0 : G) : sK0 ≠ X0 := superpose eq739 eq9
  subsumption eq741 eq739


@[equational_result]
theorem Finite.Equation10222_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation10222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ ((Z ◇ Y) ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ ((Z ◇ Y) ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ ((Z ◇ Y) ◇ Y)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ Y) ◇ ((Z ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ ((Z ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ ((Z ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = X2 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq9
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq11 eq16
  have eq52 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq11 eq18
  have eq70 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq31
  have eq90 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq52 eq70
  have eq91 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq90 eq12
  have eq122 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq90 eq91
  have eq147 (X0 X2 : G) : X0 = X2 := superpose eq122 eq122
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq10
  subsumption eq149 eq147


@[equational_result]
theorem Finite.Equation11081_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation11081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ (Z ◇ Y))) ◇ (Y ◇ (Y ◇ (X ◇ (Z ◇ Y))))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Z ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Z ◇ Y)))) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) ◇ (Z ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ s)) ◇ (Z ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ s)) ◇ (Z ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq19 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = X3 := superpose eq12 eq12
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq9 eq11
  have eq33 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq25 eq19
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq9 eq33
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq10
  subsumption eq103 eq35


@[equational_result]
theorem Finite.Equation11082_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation11082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ (Z ◇ Z))) ◇ (Y ◇ (Y ◇ (X ◇ (Z ◇ Z))))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Z ◇ Z)))) (fun s => (s ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) ◇ (Z ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ s)) ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ s)) ◇ (Z ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq9 eq9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq12 eq11
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq12 eq11
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) := superpose eq11 eq11
  have eq23 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq11 eq12
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq11 eq9
  have eq37 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := superpose eq23 eq9
  have eq42 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3)) := superpose eq23 eq12
  have eq99 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq24 eq11
  have eq154 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq23 eq37
  have eq167 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq154 eq99
  have eq176 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X3 ◇ X3)) := superpose eq167 eq42
  have eq315 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3)) = X2 := superpose eq176 eq12
  have eq379 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = X2 := superpose eq154 eq315
  have eq494 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = (((X2 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) := superpose eq21 eq12
  have eq524 (X1 X2 : G) : (((X2 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) = X1 := superpose eq379 eq494
  have eq857 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) = ((X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq12 eq20
  have eq958 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose eq524 eq524
  have eq981 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq524 eq20
  have eq1017 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq524 eq958
  have eq1026 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose eq524 eq981
  have eq1027 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) = ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq1026 eq857
  have eq1044 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq1026 eq1027
  have eq1045 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq154 eq1044
  have eq1046 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1017 eq1045
  have eq1049 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq1046 eq13
  have eq1052 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq1046 eq22
  have eq1057 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := superpose eq1046 eq37
  have eq1098 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3)) := superpose eq1046 eq1049
  have eq1101 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1046 eq1052
  have eq1105 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq1046 eq1057
  have eq1106 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1105 eq1101
  have eq1107 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) := superpose eq1106 eq1098
  have eq1116 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X1 := superpose eq1106 eq1107
  have eq1117 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq1106 eq1116
  have eq1124 (X0 X3 : G) : X0 = X3 := superpose eq1117 eq1117
  have eq1133 (X0 : G) : sK0 ≠ X0 := superpose eq1124 eq10
  subsumption eq1133 eq1124


@[equational_result]
theorem Finite.Equation11116_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation11116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ (Y ◇ Y))) ◇ (Z ◇ (Y ◇ (X ◇ (Y ◇ Y))))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Y ◇ Y)))) (fun s => (s ◇ (Z ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ (Z ◇ (Y ◇ X))) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Z ◇ s)) ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Z ◇ s)) ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ (X3 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))))) := superpose eq12 eq12
  have eq17 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq12 eq12
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = ((X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq11 eq12
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq17
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = ((X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq29 eq26
  have eq49 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X1 ◇ X1)) := superpose eq29 eq39
  have eq50 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq29 eq49
  have eq51 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq50 eq12
  have eq52 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))))) = X1 := superpose eq50 eq15
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq50 eq29
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) = X1 := superpose eq50 eq52
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq54 eq51
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) = X1 := superpose eq54 eq59
  have eq68 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq54 eq62
  have eq69 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq54 eq68
  have eq70 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X0)) = X1 := superpose eq54 eq64
  have eq71 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X0) = X1 := superpose eq54 eq70
  have eq72 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X0) = X1 := superpose eq54 eq71
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq54 eq72
  have eq80 (X0 X1 : G) : X0 = X1 := superpose eq69 eq73
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq10
  subsumption eq88 eq80


@[equational_result]
theorem Finite.Equation11205_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation11205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (Y ◇ ((Y ◇ (X ◇ (Z ◇ Y))) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Z ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Z ◇ Y)))) (fun s => (Y ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ (Z ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ Y)) ◇ (Z ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (s ◇ Y)) ◇ (Z ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq27 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq13 eq13
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq27 eq14
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq13 eq34
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq11
  subsumption eq66 eq40


@[equational_result]
theorem Finite.Equation11280_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation11280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ ((Y ◇ (Z ◇ Y)) ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ (Z ◇ Y)) ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ (Z ◇ Y)) ◇ s))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ (Z ◇ Y)) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Z ◇ Y)) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ (Z ◇ Y)) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1) = X3 := superpose eq11 eq11
  have eq22 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ X1)) = X3 := superpose eq11 eq12
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq11 eq16
  have eq54 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq42 eq22
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq11 eq54
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq10
  subsumption eq118 eq65


@[equational_result]
theorem Finite.Equation12073_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation12073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (Y ◇ (X ◇ (Z ◇ Z)))) ◇ (Y ◇ (X ◇ (Z ◇ Z)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Z ◇ Z)))) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ (Y ◇ X)) ◇ (Y ◇ X)) ◇ (Z ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ s) ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ s) ◇ s) ◇ (Z ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) = (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) := superpose eq9 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq12 eq9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq12 eq11
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq12 eq11
  have eq24 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq11 eq12
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq11 eq9
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = ((((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X0) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq11 eq12
  have eq42 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := superpose eq24 eq12
  have eq44 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq24 eq12
  have eq45 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq24 eq11
  have eq48 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) := superpose eq24 eq12
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq24 eq17
  have eq81 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq17
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq17 eq12
  have eq90 (X0 X1 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq11
  have eq99 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq71 eq45
  have eq107 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq42 eq81
  have eq108 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq90
  have eq110 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq108 eq107
  have eq112 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq110 eq86
  have eq173 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq11 eq25
  have eq262 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq110 eq173
  have eq263 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X3 ◇ X3)) := superpose eq262 eq48
  have eq420 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq22 eq22
  have eq524 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2))) = X1 := superpose eq420 eq9
  have eq1026 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq524 eq11
  have eq1151 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq20 eq17
  have eq1213 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq17 eq1151
  have eq1253 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) := superpose eq263 eq1026
  have eq1318 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = ((X2 ◇ X2) ◇ X3) := superpose eq112 eq1253
  have eq1741 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X3 ◇ X3)) = X1 := superpose eq1318 eq12
  have eq2232 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) = X2 := superpose eq263 eq42
  have eq2362 (X0 X2 X3 X4 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) = X2 := superpose eq112 eq2232
  have eq4308 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq26 eq99
  have eq4451 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq112 eq4308
  have eq4536 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4))) := superpose eq44 eq13
  have eq4537 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ (((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4))) ◇ (X5 ◇ X5))) := superpose eq18 eq13
  have eq4676 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ (X5 ◇ X5))) := superpose eq524 eq4537
  have eq4677 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X2) = (((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) := superpose eq2362 eq4676
  have eq4794 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X0 := superpose eq11 eq4451
  have eq4798 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq20 eq4451
  have eq4801 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq4451
  have eq4901 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq71 eq4794
  have eq4967 (X0 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = X2 := superpose eq4801 eq4677
  have eq4983 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq4967 eq4536
  have eq4986 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := superpose eq4901 eq4983
  have eq4988 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq4986 eq1213
  have eq4989 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq4986 eq44
  have eq5081 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq4989 eq4798
  have eq5146 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq4988 eq5081
  have eq5148 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq5146 eq12
  have eq5166 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq5148 eq110
  have eq5177 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X3 ◇ X3)) = X1 := superpose eq5166 eq1741
  have eq5181 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq5166 eq4989
  have eq5196 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) = X1 := superpose eq5166 eq5177
  have eq5197 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) = X1 := superpose eq5166 eq5196
  have eq5198 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = X1 := superpose eq5181 eq5197
  have eq5201 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X1 := superpose eq5181 eq5198
  have eq5202 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq5181 eq5201
  have eq5232 (X0 X1 : G) : X0 = X1 := superpose eq5166 eq5202
  have eq5285 (X0 : G) : sK0 ≠ X0 := superpose eq5232 eq10
  subsumption eq5285 eq5232


@[equational_result]
theorem Finite.Equation12087_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation12087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ (Y ◇ X)) ◇ Z) ◇ ((Y ◇ X) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ Z) ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Y ◇ s) ◇ Z) ◇ (s ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X3))) ◇ X0) = X2 := superpose eq8 eq10
  have eq604 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X2))) = ((X0 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq19 eq17
  have eq637 (X0 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq8 eq604
  have eq649 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq8 eq637
  have eq811 (X0 X2 : G) : X0 = X2 := superpose eq637 eq649
  have eq1059 (X0 : G) : sK0 ≠ X0 := superpose eq811 eq9
  subsumption eq1059 eq811


@[equational_result]
theorem Finite.Equation12234_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation12234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Z Y : G) : (((Z ◇ (Y ◇ X)) ◇ Y) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Z ◇ s) ◇ Y) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((Z ◇ s) ◇ Y) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X2 := superpose eq9 eq9
  have eq16 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq9 eq11
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) := superpose eq11 eq11
  have eq19 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) = X1 := superpose eq11 eq9
  have eq21 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X1 ◇ ((X0 ◇ X1) ◇ (((X3 ◇ X0) ◇ X3) ◇ X1))) := superpose eq11 eq9
  have eq35 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1)) := superpose eq19 eq11
  have eq43 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X2) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) = ((X0 ◇ X2) ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) := superpose eq19 eq17
  have eq78 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq16
  have eq81 (X0 X1 X2 : G) : (((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq17 eq11
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X2) = ((X1 ◇ X2) ◇ (((X3 ◇ ((X4 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)))) := superpose eq17 eq9
  have eq111 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) = (X0 ◇ ((X0 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq78 eq17
  have eq118 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq78 eq16
  have eq144 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X0)) := superpose eq19 eq21
  have eq169 (X0 X1 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) ◇ X1)) := superpose eq17 eq35
  have eq276 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq81 eq21
  have eq297 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq276
  have eq385 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq297 eq11
  have eq392 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq297 eq11
  have eq393 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq297 eq9
  have eq395 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq297 eq11
  have eq416 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq392 eq385
  have eq419 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq392 eq297
  have eq421 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq416 eq118
  have eq433 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq419 eq421
  have eq443 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq393 eq395
  have eq444 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq392 eq443
  have eq449 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq444 eq111
  have eq450 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1)) := superpose eq444 eq169
  have eq466 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq444 eq449
  have eq468 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq466 eq450
  have eq469 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq416 eq468
  have eq470 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq433 eq469
  have eq471 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq470 eq466
  have eq474 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq471 eq393
  have eq492 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq471 eq474
  have eq493 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq492 eq19
  have eq499 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq492 eq43
  have eq503 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq492 eq144
  have eq549 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq492 eq493
  have eq557 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq492 eq499
  have eq558 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X3 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq471 eq557
  have eq567 (X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X2) = ((X1 ◇ X2) ◇ (((X3 ◇ ((X4 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq558 eq85
  have eq715 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq492 eq503
  have eq716 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq492 eq715
  have eq717 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq716 eq11
  have eq718 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) := superpose eq716 eq18
  have eq727 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq716 eq549
  have eq749 (X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq727 eq567
  have eq752 (X1 X2 X4 : G) : (X1 ◇ X2) = ((X4 ◇ X1) ◇ X2) := superpose eq471 eq749
  have eq755 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq752 eq717
  have eq756 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3)) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3))) := superpose eq752 eq718
  have eq789 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq716 eq755
  have eq790 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq716 eq756
  have eq791 (X0 X3 : G) : (X0 ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq752 eq790
  have eq792 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq789 eq791
  have eq797 (X1 X2 X4 : G) : ((X4 ◇ X1) ◇ X2) = X1 := superpose eq792 eq752
  have eq801 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq792 eq797
  have eq802 (X0 X3 : G) : X0 = X3 := superpose eq801 eq801
  have eq807 (X0 : G) : sK0 ≠ X0 := superpose eq802 eq10
  subsumption eq807 eq802


@[equational_result]
theorem Finite.Equation12857_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation12857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (Y ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ (Y ◇ (Z ◇ Z))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Y ◇ (Z ◇ Z))) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Y ◇ (Z ◇ Z))) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq11
  have eq28 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))))) ◇ X0) = X3 := superpose eq12 eq11
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq17 eq17
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq9 eq17
  have eq53 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq34 eq28
  have eq56 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq38 eq53
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq11 eq56
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq10
  subsumption eq101 eq64


@[equational_result]
theorem Finite.Equation12883_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation12883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ Y)) ◇ (Z ◇ (Y ◇ (Y ◇ (X ◇ Y))))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ (Z ◇ (Y ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ (Z ◇ (Y ◇ (Y ◇ X)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Z ◇ (Y ◇ s))) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ (Z ◇ (Y ◇ s))) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X0)) = X1 := superpose eq11 eq11
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq12 eq11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq25 eq24
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq9 eq32
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq10
  subsumption eq85 eq39


@[equational_result]
theorem Finite.Equation13764_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation13764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ Y)) ◇ ((Z ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Z ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (s ◇ ((Z ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ ((Z ◇ Y) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ ((Z ◇ Y) ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ ((Z ◇ Y) ◇ Y)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq27 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq12 eq12
  have eq28 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq11 eq12
  have eq39 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq12 eq27
  have eq48 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq39 eq28
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq10
  subsumption eq88 eq58


@[equational_result]
theorem Finite.Equation13849_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation13849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : ((Y ◇ ((Y ◇ (X ◇ Z)) ◇ Z)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Y ◇ (s ◇ Z)) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Y ◇ (s ◇ Z)) ◇ Z))) (fun s => (s ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X Y Z : G) : ((Y ◇ (((Y ◇ X) ◇ Z) ◇ Z)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ ((s ◇ Z) ◇ Z)) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Y ◇ ((s ◇ Z) ◇ Z)) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq11 eq13
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq13 eq13
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) = X0 := superpose eq20 eq11
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) = X0 := superpose eq22 eq16
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := superpose eq22 eq27
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X2) = X0 := superpose eq22 eq36
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := superpose eq22 eq44
  have eq46 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := superpose eq22 eq38
  have eq47 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := superpose eq22 eq46
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X2 ◇ X3)) := superpose eq45 eq22
  have eq101 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X3 := superpose eq22 eq47
  have eq103 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq47 eq47
  have eq114 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X3 := superpose eq22 eq101
  have eq116 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq103 eq83
  have eq118 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq103 eq45
  have eq128 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))))) = X3 := superpose eq116 eq114
  have eq134 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X3 := superpose eq116 eq128
  have eq135 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X3 := superpose eq116 eq134
  have eq136 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := superpose eq116 eq135
  have eq137 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X1))) = X3 := superpose eq116 eq136
  have eq138 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = X3 := superpose eq116 eq137
  have eq145 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq118 eq138
  have eq148 (X0 X1 : G) : X0 = X1 := superpose eq118 eq145
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq12
  subsumption eq153 eq148


@[equational_result]
theorem Finite.Equation13992_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation13992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq14 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X Y Z : G) : (((Y ◇ ((Z ◇ X) ◇ Y)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Z ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Z ◇ s) ◇ Y))) (fun s => ((s ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X Z Y : G) : (Z ◇ (((Y ◇ (X ◇ Y)) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Z ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => (Z ◇ ((s ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq32 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq16 eq16
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq17
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq13 eq39
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq14
  subsumption eq77 eq42


@[equational_result]
theorem Finite.Equation15535_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation15535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ (Z ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((s ◇ Y) ◇ Y))) (fun s => (s ◇ (Z ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ (Z ◇ Z)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Z ◇ Z)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ Y))) (fun s => ((s ◇ (Z ◇ Z)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : ((((Y ◇ X) ◇ (Z ◇ Z)) ◇ Y) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ (Z ◇ Z)) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (((s ◇ (Z ◇ Z)) ◇ Y) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2))) ◇ (X3 ◇ X3)) = X2 := superpose eq10 eq12
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq10 eq12
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ X1) := superpose eq13 eq13
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X1) = ((X0 ◇ (X3 ◇ X3)) ◇ X1) := superpose eq10 eq13
  have eq24 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq12 eq13
  have eq27 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq10
  have eq43 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq18 eq13
  have eq69 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) ◇ X0) := superpose eq18 eq14
  have eq91 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq43 eq69
  have eq115 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq91 eq14
  have eq346 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) := superpose eq27 eq23
  have eq787 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq22 eq10
  have eq884 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq346 eq787
  have eq3709 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1))) := superpose eq12 eq24
  have eq4997 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = ((((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X3 ◇ X3)) := superpose eq22 eq16
  have eq5165 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X3 ◇ X3)) := superpose eq346 eq4997
  have eq5166 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq16 eq5165
  have eq5169 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq5166 eq884
  have eq5171 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq5166 eq5169
  have eq5172 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq5171 eq5166
  have eq5173 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq5172 eq10
  have eq5551 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq5173 eq3709
  have eq5571 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq5173 eq5551
  have eq5575 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq5571 eq115
  have eq5617 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq5575 eq5173
  have eq5634 (X0 X2 : G) : X0 = X2 := superpose eq5617 eq5617
  have eq5642 (X0 : G) : sK0 ≠ X0 := superpose eq5634 eq11
  subsumption eq5642 eq5634


@[equational_result]
theorem Finite.Equation17522_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation17522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ Z) ◇ X) ◇ (Z ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Z) ◇ s)) (fun s => (s ◇ (Z ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq10 eq8
  have eq22 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq10 eq15
  have eq42 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq15 eq8
  have eq55 (X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((X3 ◇ X2) ◇ X1) := superpose eq22 eq42
  have eq83 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2)))) = X4 := superpose eq55 eq8
  have eq105 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X1) = X4 := superpose eq22 eq83
  have eq284 (X0 X3 : G) : X0 = X3 := superpose eq8 eq105
  have eq426 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq9
  subsumption eq426 eq284


@[equational_result]
theorem Finite.Equation18212_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation18212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ Y) ◇ X) ◇ ((((Y ◇ Y) ◇ X) ◇ Z) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((s ◇ Z) ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => (s ◇ ((s ◇ Z) ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq10 eq8
  have eq21 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) := superpose eq18 eq18
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) := superpose eq10 eq18
  have eq33 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq18 eq8
  have eq39 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ X3)) = X2 := superpose eq18 eq10
  have eq40 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) = X2 := superpose eq18 eq8
  have eq71 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = (X0 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq33 eq10
  have eq189 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq21 eq10
  have eq259 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3))) := superpose eq21 eq15
  have eq280 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq24 eq259
  have eq880 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ (((X3 ◇ X3) ◇ X4) ◇ X4)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) := superpose eq21 eq71
  have eq1000 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ X3) ◇ X3) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X4) ◇ X4)) := superpose eq21 eq14
  have eq1001 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) ◇ X3)) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X2) ◇ X2) := superpose eq18 eq14
  have eq1018 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) := superpose eq18 eq14
  have eq1111 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ X3) ◇ X3) := superpose eq39 eq1000
  have eq1112 (X2 X3 : G) : (X2 ◇ X2) = ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) := superpose eq280 eq1111
  have eq1120 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X2) ◇ X2) := superpose eq10 eq1001
  have eq1147 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose eq1112 eq1018
  have eq1160 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) := superpose eq1147 eq880
  have eq1178 (X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ X2) ◇ X2) := superpose eq1160 eq1120
  have eq1345 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq8 eq1178
  have eq2038 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))))) = X2 := superpose eq1345 eq8
  have eq2096 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X2 := superpose eq8 eq2038
  have eq2099 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq2096 eq189
  have eq2115 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) = X2 := superpose eq2096 eq40
  have eq2135 (X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X2 ◇ X2)) := superpose eq2096 eq280
  have eq2180 (X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ X1) := superpose eq2096 eq2099
  have eq2339 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq2180 eq2115
  have eq2350 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq2339 eq2135
  have eq2356 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X1 := superpose eq2350 eq1178
  have eq2364 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X2 := superpose eq2350 eq2096
  have eq2385 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq2350 eq2364
  have eq2388 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq2385 eq2356
  have eq2412 (X0 X2 : G) : X0 = X2 := superpose eq2388 eq2388
  have eq2420 (X0 : G) : sK0 ≠ X0 := superpose eq2412 eq9
  subsumption eq2420 eq2412


@[equational_result]
theorem Finite.Equation19966_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation19966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((Y ◇ Y) ◇ (X ◇ Z)) ◇ (((Y ◇ Y) ◇ (X ◇ Z)) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ (s ◇ Z))) (fun s => (s ◇ (s ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((((Y ◇ Y) ◇ X) ◇ (((Y ◇ Y) ◇ X) ◇ Z)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (s ◇ Z)) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => ((s ◇ (s ◇ Z)) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq12 eq9
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq11
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq11 eq12
  have eq59 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2)) := superpose eq17 eq9
  have eq98 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq22 eq11
  have eq101 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq98
  have eq105 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq101 eq9
  have eq114 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq101 eq25
  have eq123 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq101 eq59
  have eq144 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq101 eq123
  have eq145 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq101 eq144
  have eq147 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq145 eq114
  have eq148 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq147 eq105
  have eq158 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq147 eq148
  have eq163 (X0 X1 : G) : X0 = X1 := superpose eq158 eq147
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq10
  subsumption eq165 eq163


@[equational_result]
theorem Finite.Equation20034_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation20034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq13 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X Y Z : G) : (((Y ◇ Y) ◇ ((Z ◇ X) ◇ Z)) ◇ ((Y ◇ Y) ◇ ((Z ◇ X) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ ((Z ◇ s) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ ((Z ◇ s) ◇ Z))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X Z Y : G) : ((Z ◇ (((Y ◇ Y) ◇ X) ◇ ((Y ◇ Y) ◇ X))) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ (s ◇ s)) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ Y) ◇ s)) (fun s => ((Z ◇ (s ◇ s)) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (((X3 ◇ X3) ◇ X0) ◇ ((X3 ◇ X3) ◇ X0)))) = X2 := superpose eq16 eq16
  have eq20 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = ((X3 ◇ X3) ◇ X0) := superpose eq16 eq12
  have eq34 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq16 eq20
  have eq74 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq34 eq19
  have eq122 (X0 X3 : G) : X0 = X3 := superpose eq14 eq74
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq13
  subsumption eq199 eq122


@[equational_result]
theorem Finite.Equation22455_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation22455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((Y ◇ X) ◇ ((Y ◇ Z) ◇ Y)) ◇ ((Y ◇ X) ◇ ((Y ◇ Z) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ ((Y ◇ Z) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ ((Y ◇ Z) ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ ((X ◇ ((Y ◇ Z) ◇ Y)) ◇ (X ◇ ((Y ◇ Z) ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ ((Y ◇ Z) ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ ((Y ◇ Z) ◇ Y))) (fun s => (Y ◇ (s ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq9
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X3) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X3) ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq9 eq11
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq12 eq17
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq17 eq17
  have eq32 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq11 eq17
  have eq34 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq17 eq17
  have eq41 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq30 eq18
  have eq51 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq41 eq29
  have eq56 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq51 eq32
  have eq57 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq34 eq56
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq17 eq57
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq10
  subsumption eq95 eq62


@[equational_result]
theorem Finite.Equation22619_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation22619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (Y ◇ ((Y ◇ X) ◇ ((Z ◇ Z) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ ((Z ◇ Z) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ ((Z ◇ Z) ◇ Z))) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ (Y ◇ (X ◇ ((Z ◇ Z) ◇ Z)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ ((Z ◇ Z) ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ ((Z ◇ Z) ◇ Z))) (fun s => (Y ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq11
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq12 eq12
  have eq27 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := superpose eq12 eq16
  have eq37 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq27 eq11
  have eq42 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq27 eq20
  have eq51 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq42
  have eq53 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq51 eq27
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq51 eq53
  have eq58 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq57 eq37
  have eq61 (X0 X2 : G) : X0 = X2 := superpose eq58 eq58
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq10
  subsumption eq63 eq61


@[equational_result]
theorem Finite.Equation22634_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation22634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((Y ◇ (Y ◇ Y)) ◇ (X ◇ Z)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Y)) ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Y ◇ Y)) ◇ (s ◇ Z))) (fun s => (s ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((((Y ◇ (Y ◇ Y)) ◇ X) ◇ Z) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Z) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Y ◇ Y)) ◇ s)) (fun s => ((s ◇ Z) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq12 eq12
  have eq27 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq12 eq16
  have eq37 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq27 eq11
  have eq42 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X0 ◇ X0) := superpose eq27 eq20
  have eq51 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq42
  have eq53 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq51 eq27
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq51 eq53
  have eq58 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq57 eq37
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq58 eq58
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq10
  subsumption eq66 eq64


@[equational_result]
theorem Finite.Equation22818_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation22818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((Y ◇ (Z ◇ Y)) ◇ (X ◇ Y)) ◇ ((Y ◇ (Z ◇ Y)) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Z ◇ Y)) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Z ◇ Y)) ◇ (s ◇ Y))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((((Y ◇ (Z ◇ Y)) ◇ X) ◇ ((Y ◇ (Z ◇ Y)) ◇ X)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Z ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Z ◇ Y)) ◇ s)) (fun s => ((s ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1) = X3 := superpose eq12 eq12
  have eq17 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ X1)) = X3 := superpose eq12 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = (((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0)) := superpose eq9 eq11
  have eq33 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq12 eq17
  have eq34 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq17 eq17
  have eq36 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0)) = (X1 ◇ X3) := superpose eq17 eq11
  have eq41 (X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ (X3 ◇ X1)) := superpose eq34 eq21
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq41 eq33
  have eq56 (X0 X1 X3 : G) : (X1 ◇ X3) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq53 eq36
  have eq57 (X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ X3) := superpose eq34 eq56
  have eq62 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq17 eq57
  have eq79 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq41 eq15
  have eq87 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq62 eq79
  have eq92 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq87 eq62
  have eq94 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq87 eq15
  have eq99 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X3 := superpose eq92 eq17
  have eq105 (X1 X3 : G) : (X3 ◇ X1) = X3 := superpose eq99 eq94
  have eq111 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq105 eq87
  have eq119 (X0 X1 : G) : X0 = X1 := superpose eq105 eq111
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq10
  subsumption eq121 eq119


@[equational_result]
theorem Finite.Equation25964_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation25964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ (Z ◇ Z)) ◇ ((Y ◇ (X ◇ Y)) ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (s ◇ Y)) ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (s ◇ Y)) ◇ (Z ◇ Z))) (fun s => (s ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : (Y ◇ (((X ◇ (Z ◇ Z)) ◇ (X ◇ (Z ◇ Z))) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Z ◇ Z))) (fun s => (Y ◇ ((s ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X0) = X2 := superpose eq14 eq14
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq14 eq10
  have eq30 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := superpose eq14 eq18
  have eq71 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq30 eq17
  have eq118 (X0 X3 : G) : X0 = X3 := superpose eq12 eq71
  have eq197 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq11
  subsumption eq197 eq118


@[equational_result]
theorem Finite.Equation26105_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation26105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ ((Y ◇ X) ◇ (Z ◇ Z))) ◇ ((Y ◇ X) ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ (Z ◇ Z))) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq9 eq9
  have eq24 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq11
  have eq92 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq24 eq11
  have eq100 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq92
  have eq104 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = X0 := superpose eq100 eq9
  have eq107 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) = X2 := superpose eq100 eq13
  have eq133 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq100 eq107
  have eq134 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq104 eq133
  have eq135 (X0 X3 : G) : X0 = X3 := superpose eq134 eq134
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq135 eq10
  subsumption eq149 eq135


@[equational_result]
theorem Finite.Equation27859_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation27859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ (Y ◇ (X ◇ (Z ◇ Z)))) ◇ (X ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Z ◇ Z))) (fun s => ((Y ◇ (Y ◇ s)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq8 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X2 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq8 eq10
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq10 eq8
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq18 eq18
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) := superpose eq10 eq18
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq18 eq8
  have eq73 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq33 eq10
  have eq259 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) := superpose eq21 eq14
  have eq280 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) := superpose eq24 eq259
  have eq880 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) = ((X4 ◇ (X4 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq21 eq73
  have eq1003 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq16 eq15
  have eq1083 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq73 eq280
  have eq1164 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq1083 eq1003
  have eq1195 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) := superpose eq1164 eq880
  have eq1258 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) := superpose eq8 eq1164
  have eq1828 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X3 ◇ X3)) = X2 := superpose eq1258 eq8
  have eq1885 (X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ X3)) = X2 := superpose eq8 eq1828
  have eq1898 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) = X0 := superpose eq1885 eq1195
  have eq2110 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = X0 := superpose eq1885 eq1898
  have eq2111 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq1885 eq2110
  have eq2117 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X1 := superpose eq2111 eq1164
  have eq2143 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq2111 eq2117
  have eq2153 (X0 X2 : G) : X0 = X2 := superpose eq2143 eq2143
  have eq2179 (X0 : G) : sK0 ≠ X0 := superpose eq2153 eq9
  subsumption eq2179 eq2153


@[equational_result]
theorem Finite.Equation28770_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation28770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ Y) ◇ Y) ◇ (X ◇ (Y ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ (Y ◇ Z))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ (Y ◇ Z))) (fun s => (((Y ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq10 eq8
  have eq22 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq15
  have eq40 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) := superpose eq15 eq8
  have eq55 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = (X1 ◇ (X0 ◇ X4)) := superpose eq22 eq40
  have eq79 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) = X3 := superpose eq55 eq8
  have eq105 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X3 := superpose eq22 eq79
  have eq284 (X0 X3 : G) : X0 = X3 := superpose eq8 eq105
  have eq426 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq9
  subsumption eq426 eq284


@[equational_result]
theorem Finite.Equation30591_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation30591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Z Y : G) : ((Z ◇ Z) ◇ ((Y ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ (Y ◇ s)) ◇ Y)) (fun s => ((Z ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : (Y ◇ ((Z ◇ Z) ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Z ◇ Z) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (Y ◇ ((Z ◇ Z) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X Y Z : G) : (Y ◇ (Y ◇ ((Z ◇ Z) ◇ (X ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Y ◇ ((Z ◇ Z) ◇ s)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (Y ◇ ((Z ◇ Z) ◇ s)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq13 eq13
  have eq19 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq11 eq13
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = ((X3 ◇ X3) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq14 eq14
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = (X1 ◇ ((X3 ◇ X3) ◇ X0)) := superpose eq11 eq14
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq13 eq14
  have eq26 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq14 eq14
  have eq27 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq14 eq11
  have eq28 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq14 eq13
  have eq44 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq19 eq14
  have eq50 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X3 ◇ X3)) = X2 := superpose eq19 eq11
  have eq73 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq19 eq15
  have eq93 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq44 eq73
  have eq113 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq93 eq13
  have eq114 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq93 eq15
  have eq167 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq19 eq114
  have eq345 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := superpose eq27 eq24
  have eq351 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq114 eq24
  have eq352 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X5 ◇ X5) ◇ ((X4 ◇ X4) ◇ X2))) = (X3 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq24 eq24
  have eq493 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X3 ◇ X3)) := superpose eq167 eq351
  have eq598 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X2))) = X1 := superpose eq493 eq13
  have eq694 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq93 eq23
  have eq834 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq345 eq694
  have eq835 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X1 := superpose eq834 eq598
  have eq839 (X1 X2 X3 : G) : (((X3 ◇ X3) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) = X2 := superpose eq834 eq50
  have eq846 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X5 ◇ X5) ◇ ((X4 ◇ X4) ◇ X2))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq834 eq352
  have eq854 (X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X1))) = (X3 ◇ (X2 ◇ (X4 ◇ X4))) := superpose eq834 eq846
  have eq1002 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq28 eq28
  have eq1174 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X1 := superpose eq835 eq1002
  have eq3972 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X4))) ◇ X3) = X4 := superpose eq854 eq11
  have eq4412 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1) = (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1) ◇ X0) := superpose eq13 eq25
  have eq4717 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3))) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq1174 eq18
  have eq4775 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq839 eq4717
  have eq4776 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq834 eq4775
  have eq4903 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))))) := superpose eq26 eq15
  have eq4909 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = ((X3 ◇ X3) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq26 eq23
  have eq4967 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = ((X3 ◇ X3) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq4776 eq4909
  have eq4968 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = X1 := superpose eq113 eq4967
  have eq4969 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq4968 eq4903
  have eq4980 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq854 eq4969
  have eq5240 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq839 eq4980
  have eq5244 (X0 X3 X4 : G) : ((X3 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X3) = X4 := superpose eq5240 eq3972
  have eq5280 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq5244 eq4412
  have eq5295 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq5280 eq13
  have eq5711 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq5280 eq5295
  have eq5712 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq5280 eq5711
  have eq5715 (X0 X3 : G) : X0 = X3 := superpose eq5712 eq5712
  have eq5721 (X0 : G) : sK0 ≠ X0 := superpose eq5715 eq12
  subsumption eq5721 eq5715


@[equational_result]
theorem Finite.Equation32280_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation32280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X Y Z : G) : (Y ◇ ((Y ◇ (Y ◇ (X ◇ Y))) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ (Y ◇ s)) ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ ((Y ◇ (Y ◇ s)) ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq16
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq11 eq36
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq12
  subsumption eq89 eq42


@[equational_result]
theorem Finite.Equation32281_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation32281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (Y ◇ ((Y ◇ ((Y ◇ X) ◇ Z)) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ ((Y ◇ s) ◇ Z)) ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ ((Y ◇ s) ◇ Z)) ◇ Z)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X Y Z : G) : ((Y ◇ (Y ◇ ((Y ◇ X) ◇ Z))) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ s)) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Z)) (fun s => ((Y ◇ (Y ◇ s)) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X3)) = X2 := superpose eq11 eq13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq13
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq13 eq13
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3)) ◇ X3)) = X2 := superpose eq20 eq18
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) ◇ X3)) = X2 := superpose eq20 eq25
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq22 eq13
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := superpose eq22 eq15
  have eq39 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ ((X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3))) ◇ X3)) = X2 := superpose eq22 eq29
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := superpose eq22 eq33
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := superpose eq22 eq48
  have eq59 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) ◇ X3))) = X2 := superpose eq22 eq39
  have eq60 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X3) ◇ X3)))) = X2 := superpose eq22 eq59
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3))))) = X2 := superpose eq22 eq60
  have eq62 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)))))) = X2 := superpose eq22 eq61
  have eq63 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))))))) = X2 := superpose eq22 eq62
  have eq64 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))))))) = X2 := superpose eq22 eq63
  have eq109 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) := superpose eq36 eq49
  have eq113 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq49 eq49
  have eq115 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq49 eq49
  have eq121 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X2 := superpose eq49 eq36
  have eq123 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq49 eq109
  have eq127 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X2 := superpose eq123 eq64
  have eq133 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X2 := superpose eq123 eq127
  have eq143 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq22 eq113
  have eq144 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq22 eq143
  have eq151 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq115 eq133
  have eq153 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq115 eq144
  have eq165 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq115 eq121
  have eq166 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq123 eq165
  have eq167 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq166 eq153
  have eq168 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq167 eq151
  have eq187 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq167 eq168
  have eq192 (X0 X1 : G) : X0 = X1 := superpose eq167 eq187
  have eq197 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq12
  subsumption eq197 eq192


@[equational_result]
theorem Finite.Equation32294_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation32294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (Y ◇ Z)) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Z)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => ((Y ◇ (Y ◇ Z)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ ((Y ◇ (Y ◇ Z)) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Y ◇ (Y ◇ Z)) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ ((Y ◇ (Y ◇ Z)) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq24 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))) = X3 := superpose eq12 eq12
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq11 eq12
  have eq35 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq12 eq24
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq35 eq25
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq10
  subsumption eq88 eq58


@[equational_result]
theorem Finite.Equation33020_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation33020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((((Y ◇ X) ◇ Y) ◇ Y) ◇ Z) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((s ◇ Y) ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (((s ◇ Y) ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ ((((X ◇ Y) ◇ Y) ◇ Z) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (((s ◇ Y) ◇ Z) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (Y ◇ (((s ◇ Y) ◇ Z) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq12 eq11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = X1 := superpose eq21 eq20
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq9 eq31
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq10
  subsumption eq85 eq39


@[equational_result]
theorem Finite.Equation33436_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation33436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Z Y : G) : (((Z ◇ Z) ◇ Y) ◇ ((Y ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Z ◇ Z) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((Y ◇ s) ◇ Y)) (fun s => (((Z ◇ Z) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose eq12 eq12
  have eq33 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X3) ◇ X1)) = X3 := superpose eq10 eq15
  have eq53 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq33 eq16
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq15 eq53
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq11
  subsumption eq101 eq64


@[equational_result]
theorem Finite.Equation33883_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation33883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ (X ◇ Y)) ◇ (Y ◇ ((X ◇ Y) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ (s ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ (Y ◇ (s ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2)))) = X1 := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) = (((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq8 eq8
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq8 eq10
  have eq17 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq10 eq10
  have eq18 (X0 X1 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq10 eq8
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq10 eq8
  have eq30 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq17 eq18
  have eq33 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq18 eq10
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)) = ((X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2)) ◇ (X1 ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X3))) := superpose eq18 eq14
  have eq77 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq14 eq17
  have eq82 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := superpose eq14 eq10
  have eq83 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4))) ◇ (X0 ◇ X1)) := superpose eq14 eq8
  have eq111 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq77 eq14
  have eq136 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq14 eq19
  have eq139 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) = (((((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1))) ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq17 eq19
  have eq159 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) = ((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq33
  have eq274 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq82 eq19
  have eq294 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq274
  have eq296 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) = (((X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X3) := superpose eq17 eq12
  have eq338 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (((((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)))) := superpose eq33 eq12
  have eq380 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq294 eq10
  have eq389 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq294 eq18
  have eq391 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq294 eq10
  have eq393 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq294 eq8
  have eq394 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq294 eq10
  have eq411 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq380 eq294
  have eq437 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq380 eq391
  have eq441 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq380 eq394
  have eq446 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq441 eq111
  have eq447 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq441 eq159
  have eq463 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq441 eq446
  have eq465 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq463 eq447
  have eq466 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq437 eq465
  have eq467 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq466 eq389
  have eq469 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq467 eq463
  have eq470 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq469 eq467
  have eq472 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq411 eq470
  have eq482 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq472 eq393
  have eq499 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq472 eq482
  have eq502 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq499 eq30
  have eq509 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)))) := superpose eq499 eq338
  have eq518 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq499 eq139
  have eq521 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2))) = (((X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X3) := superpose eq499 eq296
  have eq530 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3))) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)) := superpose eq499 eq42
  have eq560 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)) = X0 := superpose eq499 eq502
  have eq561 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) = X0 := superpose eq472 eq560
  have eq565 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq499 eq509
  have eq585 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X3))) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq499 eq530
  have eq586 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq472 eq585
  have eq607 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4))) ◇ (X0 ◇ X1)) := superpose eq586 eq83
  have eq610 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq586 eq136
  have eq656 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq586 eq565
  have eq728 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq656 eq610
  have eq734 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq728 eq518
  have eq736 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) = (((X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X3) := superpose eq728 eq521
  have eq737 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq728 eq561
  have eq784 (X0 X1 X2 : G) : (X1 ◇ X0) = (((((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq728 eq734
  have eq785 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq728 eq737
  have eq786 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq728 eq785
  have eq787 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := superpose eq786 eq607
  have eq789 (X0 X1 X2 : G) : (X1 ◇ X0) = (((((X2 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq787 eq784
  have eq790 (X0 X1 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (((X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ (X3 ◇ X0)) ◇ X3) := superpose eq787 eq736
  have eq826 (X0 X1 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (((X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X3) ◇ X3) := superpose eq787 eq790
  have eq827 (X0 X1 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X3) := superpose eq499 eq826
  have eq828 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) := superpose eq728 eq827
  have eq829 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq728 eq828
  have eq830 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq728 eq829
  have eq831 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X2 ◇ X0) ◇ X0) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq830 eq789
  have eq835 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq499 eq831
  have eq839 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X1 := superpose eq835 eq787
  have eq842 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq835 eq839
  have eq843 (X0 X3 : G) : X0 = X3 := superpose eq842 eq842
  have eq848 (X0 : G) : sK0 ≠ X0 := superpose eq843 eq9
  subsumption eq848 eq843


@[equational_result]
theorem Finite.Equation33884_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation33884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ (X ◇ Z)) ◇ (Y ◇ ((X ◇ Z) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ (s ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => ((Y ◇ s) ◇ (Y ◇ (s ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ X3))) = X2 := superpose eq8 eq10
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq10 eq8
  have eq30 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq20 eq10
  have eq342 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq14 eq30
  have eq366 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq342 eq342
  have eq533 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq8 eq366
  have eq687 (X0 X2 : G) : X0 = X2 := superpose eq366 eq533
  have eq890 (X0 : G) : sK0 ≠ X0 := superpose eq687 eq9
  subsumption eq890 eq687


@[equational_result]
theorem Finite.Equation33998_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation33998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((((Y ◇ Y) ◇ X) ◇ Z) ◇ ((((Y ◇ Y) ◇ X) ◇ Z) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ s) ◇ Z)) (fun s => (s ◇ (s ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ Y) ◇ ((X ◇ Z) ◇ ((X ◇ Z) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ (s ◇ (s ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => ((Y ◇ Y) ◇ (s ◇ (s ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X3) := superpose eq9 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq12 eq9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)))) := superpose eq12 eq11
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq11 eq12
  have eq25 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq11 eq9
  have eq26 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X3) ◇ X3)))) := superpose eq11 eq12
  have eq42 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose eq24 eq12
  have eq45 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) = X2 := superpose eq24 eq11
  have eq46 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq24 eq12
  have eq51 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose eq24 eq12
  have eq72 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq17 eq17
  have eq80 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ X2) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq24 eq17
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq12
  have eq89 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq17 eq11
  have eq100 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq42 eq72
  have eq105 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) = X2 := superpose eq80 eq45
  have eq108 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq11 eq89
  have eq110 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq108 eq100
  have eq112 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq110 eq86
  have eq168 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) := superpose eq11 eq25
  have eq259 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X2 ◇ X2) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose eq112 eq168
  have eq260 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq259 eq51
  have eq419 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq22 eq22
  have eq536 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) = X2 := superpose eq419 eq9
  have eq2251 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X4))) = X4 := superpose eq260 eq42
  have eq2368 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X4))) = X4 := superpose eq112 eq2251
  have eq4301 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) = ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) := superpose eq26 eq105
  have eq4436 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (((X1 ◇ X1) ◇ X2) ◇ X2) := superpose eq112 eq4301
  have eq4545 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) = (((X5 ◇ X5) ◇ (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)))) ◇ ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X4))) := superpose eq18 eq13
  have eq4554 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = (((X4 ◇ X4) ◇ (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X2 ◇ X2))) ◇ ((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X0))) := superpose eq46 eq13
  have eq4674 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) = (((X5 ◇ X5) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) ◇ ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X4))) := superpose eq536 eq4545
  have eq4675 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X4))) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) := superpose eq2368 eq4674
  have eq4777 (X0 X1 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq11 eq4436
  have eq4783 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := superpose eq12 eq4436
  have eq4885 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq80 eq4777
  have eq4946 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) = X3 := superpose eq4783 eq4675
  have eq4958 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X0))) := superpose eq4946 eq4554
  have eq4963 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq4885 eq4958
  have eq4970 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq4963 eq46
  have eq5127 (X0 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq4970 eq11
  have eq5179 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq5127 eq4783
  have eq5203 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq5179 eq4970
  have eq5227 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq5203 eq5127
  have eq5231 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq5203 eq5227
  have eq5236 (X0 X2 : G) : X0 = X2 := superpose eq5231 eq5231
  have eq5244 (X0 : G) : sK0 ≠ X0 := superpose eq5236 eq10
  subsumption eq5244 eq5236


@[equational_result]
theorem Finite.Equation34778_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation34778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (Y ◇ ((X ◇ ((Y ◇ Z) ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ ((Y ◇ Z) ◇ Y)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ ((Y ◇ Z) ◇ Y)) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ (X ◇ Y)) ◇ ((Y ◇ Z) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ ((Y ◇ Z) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ s) ◇ ((Y ◇ Z) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X2 := superpose eq11 eq11
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq12 eq12
  have eq43 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq16
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq43 eq26
  have eq60 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq43 eq54
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq11 eq60
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq10
  subsumption eq121 eq68


@[equational_result]
theorem Finite.Equation34888_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation34888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((((Y ◇ Y) ◇ X) ◇ Y) ◇ Z) ◇ (((Y ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ s) ◇ Y)) (fun s => ((s ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ Y) ◇ (((X ◇ Y) ◇ Z) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ ((s ◇ Z) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ Y) ◇ ((s ◇ Z) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq12 eq12
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq12 eq12
  have eq19 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq9 eq11
  have eq26 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) = (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq11 eq12
  have eq28 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq15
  have eq34 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq28 eq19
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) := superpose eq28 eq26
  have eq46 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq28 eq35
  have eq47 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq28 eq46
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq47 eq34
  have eq49 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq47 eq17
  have eq50 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X0 := superpose eq47 eq12
  have eq51 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq47 eq15
  have eq52 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq47 eq28
  have eq53 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) = X1 := superpose eq47 eq49
  have eq54 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq51 eq48
  have eq55 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq54 eq50
  have eq56 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X3) ◇ X0)) = X1 := superpose eq54 eq53
  have eq59 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq54 eq56
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq52 eq55
  have eq63 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq52 eq59
  have eq73 (X0 X1 : G) : X0 = X1 := superpose eq62 eq63
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq10
  subsumption eq81 eq73


@[equational_result]
theorem Finite.Equation34889_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation34889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((((Y ◇ Y) ◇ X) ◇ Z) ◇ Z) ◇ (((Y ◇ Y) ◇ X) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Y) ◇ s) ◇ Z)) (fun s => ((s ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ Y) ◇ (((X ◇ Z) ◇ Z) ◇ (X ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ ((s ◇ Z) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => ((Y ◇ Y) ◇ ((s ◇ Z) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq9 eq9
  have eq20 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = (((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq12 eq11
  have eq21 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0) := superpose eq11 eq11
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq12 eq11
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ X0) := superpose eq11 eq12
  have eq24 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (((X1 ◇ X1) ◇ X0) ◇ X3) := superpose eq11 eq9
  have eq37 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X1 := superpose eq23 eq9
  have eq47 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq23 eq12
  have eq96 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1)) := superpose eq24 eq11
  have eq154 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq23 eq37
  have eq175 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq154 eq96
  have eq176 (X0 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq175 eq47
  have eq327 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X3 := superpose eq176 eq12
  have eq391 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X3) ◇ (X1 ◇ X1))) = X3 := superpose eq154 eq327
  have eq497 (X0 X1 X2 X3 : G) : (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X3))) = ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) := superpose eq22 eq12
  have eq527 (X2 X3 : G) : (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X3))) = X2 := superpose eq391 eq497
  have eq984 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq527 eq20
  have eq1032 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq527 eq984
  have eq1033 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq1032 eq12
  have eq1051 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq1033 eq154
  have eq1055 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq1051 eq21
  have eq1059 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq1051 eq14
  have eq1065 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq1051 eq37
  have eq1111 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq1051 eq1055
  have eq1113 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq1051 eq1059
  have eq1118 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq1051 eq1065
  have eq1119 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1118 eq1111
  have eq1122 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq1119 eq1113
  have eq1133 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq1119 eq1122
  have eq1179 (X0 X2 : G) : X0 = X2 := superpose eq1133 eq1133
  have eq1199 (X0 : G) : sK0 ≠ X0 := superpose eq1179 eq10
  subsumption eq1199 eq1179


@[equational_result]
theorem Finite.Equation35036_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation35036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((((Y ◇ Z) ◇ X) ◇ Y) ◇ Y) ◇ (((Y ◇ Z) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Z) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Z) ◇ s) ◇ Y)) (fun s => ((s ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ Z) ◇ (((X ◇ Y) ◇ Y) ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Z) ◇ ((s ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ Z) ◇ ((s ◇ Y) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq12 eq12
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq9 eq11
  have eq34 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq25 eq16
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq9 eq34
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq10
  subsumption eq116 eq35


@[equational_result]
theorem Finite.Equation35100_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation35100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : ((Y ◇ (((Y ◇ Z) ◇ X) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ Z) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ Z) ◇ s) ◇ Y)) (fun s => ((Y ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : ((Y ◇ Z) ◇ ((Y ◇ (X ◇ Y)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Z) ◇ ((Y ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ Z) ◇ ((Y ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq27 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq13 eq13
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq27 eq14
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq13 eq34
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq11
  subsumption eq66 eq40


@[equational_result]
theorem Finite.Equation35685_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation35685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ ((X ◇ Y) ◇ Z)) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ Z)) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (s ◇ Z)) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)))) := superpose eq8 eq10
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = X1 := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X0)) := superpose eq8 eq10
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq10 eq8
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X3)) = (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X1) := superpose eq10 eq8
  have eq88 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq8 eq15
  have eq89 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq10 eq15
  have eq94 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq15 eq18
  have eq105 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3))) := superpose eq15 eq18
  have eq125 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq94 eq18
  have eq248 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ X1) ◇ (((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)))) = X0 := superpose eq8 eq14
  have eq249 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ X3) ◇ (((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3)))) := superpose eq20 eq14
  have eq266 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3)) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3)) ◇ X0))) := superpose eq15 eq14
  have eq276 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq14 eq20
  have eq304 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))) := superpose eq15 eq89
  have eq323 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq89 eq20
  have eq346 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := superpose eq8 eq323
  have eq475 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq346 eq15
  have eq478 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq346 eq88
  have eq485 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq346 eq14
  have eq488 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq346 eq16
  have eq514 (X0 X1 X2 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ X1) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)))) = X0 := superpose eq488 eq248
  have eq520 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq488 eq276
  have eq526 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq488 eq14
  have eq581 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq485 eq526
  have eq583 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq581 eq520
  have eq584 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq581 eq475
  have eq587 (X0 X1 X2 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ X1) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ X0)) = X0 := superpose eq581 eq514
  have eq593 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X0 ◇ X3))) := superpose eq581 eq304
  have eq594 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X0))) := superpose eq581 eq266
  have eq598 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3))) := superpose eq581 eq105
  have eq601 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq581 eq125
  have eq602 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ X3) ◇ (((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq581 eq249
  have eq604 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq581 eq478
  have eq772 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq581 eq583
  have eq773 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq581 eq772
  have eq778 (X0 X1 X2 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ (((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) = X0 := superpose eq581 eq587
  have eq779 (X0 X1 X2 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) ◇ X0)) = X0 := superpose eq581 eq778
  have eq806 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0)) := superpose eq581 eq593
  have eq807 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))))) := superpose eq581 eq594
  have eq808 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) := superpose eq581 eq807
  have eq809 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq581 eq808
  have eq810 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq581 eq809
  have eq811 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq581 eq810
  have eq812 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq581 eq811
  have eq813 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) := superpose eq581 eq812
  have eq814 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) := superpose eq581 eq813
  have eq815 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) := superpose eq581 eq814
  have eq816 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) := superpose eq581 eq815
  have eq833 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0)) := superpose eq581 eq598
  have eq834 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq581 eq833
  have eq835 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq581 eq834
  have eq836 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq816 eq835
  have eq847 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq581 eq601
  have eq848 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq581 eq847
  have eq849 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq581 eq848
  have eq850 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq581 eq849
  have eq851 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ X3) ◇ (((((X3 ◇ X4) ◇ X1) ◇ ((X3 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X3) ◇ X0)) := superpose eq581 eq602
  have eq852 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((((X3 ◇ X4) ◇ X1) ◇ (X3 ◇ X4)) ◇ X3) ◇ X3) ◇ (((((X3 ◇ X4) ◇ X1) ◇ (X3 ◇ X4)) ◇ X3) ◇ X0)) := superpose eq581 eq851
  have eq853 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((((((X3 ◇ X4) ◇ X1) ◇ X3) ◇ X3) ◇ X3) ◇ (((((X3 ◇ X4) ◇ X1) ◇ X3) ◇ X3) ◇ X0)) := superpose eq581 eq852
  have eq856 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq581 eq604
  have eq857 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq850 eq856
  have eq858 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq581 eq857
  have eq859 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq581 eq858
  have eq861 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq859 eq773
  have eq865 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq859 eq584
  have eq867 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) := superpose eq859 eq816
  have eq868 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = ((X0 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq859 eq836
  have eq869 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq859 eq850
  have eq871 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq859 eq861
  have eq872 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq859 eq871
  have eq875 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq859 eq865
  have eq876 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq859 eq875
  have eq877 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq876 eq872
  have eq879 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq877 eq859
  have eq885 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := superpose eq877 eq867
  have eq886 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq877 eq868
  have eq887 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) := superpose eq879 eq869
  have eq888 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq877 eq887
  have eq890 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq888 eq779
  have eq894 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X3 ◇ X3) ◇ (X3 ◇ X0)) := superpose eq888 eq853
  have eq897 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq877 eq890
  have eq899 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X3 ◇ (X3 ◇ X0)) := superpose eq877 eq894
  have eq900 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq897 eq899
  have eq901 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq900 eq886
  have eq904 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) = X0 := superpose eq901 eq885
  have eq908 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq904 eq806
  have eq909 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq877 eq908
  have eq919 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq909 eq897
  have eq991 (X0 X2 : G) : X0 = X2 := superpose eq919 eq919
  have eq1005 (X0 : G) : sK0 ≠ X0 := superpose eq991 eq9
  subsumption eq1005 eq991


@[equational_result]
theorem Finite.Equation35836_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation35836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (Y ◇ (((Y ◇ (Y ◇ Z)) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ (Y ◇ Z)) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ (Y ◇ Z)) ◇ s) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((Y ◇ (Y ◇ Z)) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Z)) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (Y ◇ Z)) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) = X3 := superpose eq11 eq11
  have eq19 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ X1) = X3 := superpose eq11 eq9
  have eq32 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq11 eq16
  have eq49 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ X1) = X3 := superpose eq11 eq19
  have eq71 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq32
  have eq91 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq49 eq71
  have eq94 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X3 := superpose eq91 eq16
  have eq132 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq91 eq94
  have eq133 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq91 eq132
  have eq135 (X0 X2 : G) : X0 = X2 := superpose eq133 eq133
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq135 eq10
  subsumption eq137 eq135


@[equational_result]
theorem Finite.Equation36487_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ ((X ◇ (Y ◇ Z)) ◇ Y)) ◇ ((X ◇ (Y ◇ Z)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ (Y ◇ Z)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ (Y ◇ Z)) ◇ Y)) (fun s => ((Y ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ (X ◇ Y)) ◇ (Y ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ s) ◇ (Y ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ s) ◇ (Y ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq11 eq12
  have eq30 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ (X1 ◇ X3)) ◇ X1) := superpose eq11 eq9
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = (((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3)) := superpose eq11 eq12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) := superpose eq9 eq29
  have eq57 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X1 := superpose eq29 eq12
  have eq67 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X0) := superpose eq29 eq9
  have eq85 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq35 eq13
  have eq129 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X3))) = X1 := superpose eq30 eq9
  have eq168 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4)) = X1 := superpose eq29 eq57
  have eq182 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq9 eq57
  have eq217 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ X2) := superpose eq168 eq67
  have eq225 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3))) = X1 := superpose eq9 eq85
  have eq246 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3))) := superpose eq85 eq85
  have eq288 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq168 eq225
  have eq312 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) = X0 := superpose eq9 eq217
  have eq318 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq85 eq217
  have eq413 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq312 eq182
  have eq416 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3))) := superpose eq312 eq246
  have eq453 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq318 eq416
  have eq454 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq413 eq453
  have eq455 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq288 eq454
  have eq460 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq455 eq318
  have eq468 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3)) := superpose eq460 eq32
  have eq469 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X3))) = X1 := superpose eq460 eq129
  have eq524 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq460 eq468
  have eq525 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq460 eq524
  have eq526 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq460 eq525
  have eq527 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq460 eq526
  have eq528 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq460 eq527
  have eq529 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq460 eq469
  have eq530 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X1 := superpose eq460 eq529
  have eq531 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq460 eq530
  have eq532 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq460 eq531
  have eq539 (X0 X1 : G) : X0 = X1 := superpose eq528 eq532
  have eq544 (X0 : G) : sK0 ≠ X0 := superpose eq539 eq10
  subsumption eq544 eq539


@[equational_result]
theorem Finite.Equation36514_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ Y) ◇ ((X ◇ Y) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ Y) ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ Y) ◇ (s ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) = ((((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) ◇ X0) ◇ X1) := superpose eq8 eq8
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2)) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X3)) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq8 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1) ◇ X0) := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq10 eq8
  have eq20 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) ◇ X0) = (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) ◇ ((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) := superpose eq8 eq14
  have eq31 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X3)) := superpose eq14 eq14
  have eq42 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq8
  have eq123 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq42 eq17
  have eq140 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X3) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq42 eq15
  have eq142 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = (((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X4)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X5)) := superpose eq14 eq15
  have eq155 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) ◇ X1) = ((((((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ X4) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ (((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ X4)) ◇ X0) := superpose eq8 eq15
  have eq157 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2)) ◇ X2) = (((((((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2) ◇ X4) ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ ((((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2) ◇ X4)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq15 eq15
  have eq168 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) = X0 := superpose eq15 eq10
  have eq219 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) ◇ X1) := superpose eq14 eq16
  have eq223 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X2 ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq15 eq16
  have eq320 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq42 eq168
  have eq395 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq20 eq320
  have eq446 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = (((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4))) ◇ X2) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4))) := superpose eq15 eq12
  have eq715 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X3)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq31 eq15
  have eq721 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) = (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) ◇ (X0 ◇ X4)) := superpose eq31 eq15
  have eq723 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq31 eq17
  have eq729 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X3) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq31 eq10
  have eq858 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq13 eq19
  have eq874 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = (((X0 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq19 eq19
  have eq875 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) ◇ (((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X0 ◇ X4))) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq15 eq19
  have eq921 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) ◇ (((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X5)) := superpose eq19 eq15
  have eq938 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq858 eq874
  have eq939 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq938 eq19
  have eq950 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq939 eq223
  have eq967 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq939 eq123
  have eq1007 (X0 X1 X2 X4 X5 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq938 eq921
  have eq1008 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq10 eq1007
  have eq1035 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1)) = X0 := superpose eq10 eq939
  have eq1106 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ X2) = ((((((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq939 eq15
  have eq1119 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X4))) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq939 eq219
  have eq1125 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq939 eq17
  have eq1126 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = X2 := superpose eq939 eq10
  have eq1168 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq1035 eq950
  have eq1173 (X0 X1 X2 X3 : G) : ((X2 ◇ (((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2)) ◇ X2) = (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq1168 eq157
  have eq1217 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ X2) := superpose eq1008 eq1106
  have eq1234 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq939 eq1125
  have eq1237 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1)) = ((((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ (X2 ◇ X3)) ◇ X2) := superpose eq1234 eq1119
  have eq1245 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1217 eq1237
  have eq1250 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = ((((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq1245 eq875
  have eq1254 (X0 X1 X2 X3 : G) : ((X2 ◇ (((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2)) ◇ X2) = ((((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq1245 eq1173
  have eq1272 (X0 X1 X2 X3 : G) : ((X2 ◇ (((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2)) ◇ X2) = X0 := superpose eq1126 eq1254
  have eq1273 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq1126 eq1250
  have eq1277 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq1273 eq723
  have eq1340 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq1273 eq1277
  have eq1343 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq1340 eq42
  have eq1350 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X4)) := superpose eq1340 eq140
  have eq1356 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X4)) := superpose eq1340 eq395
  have eq1364 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq1340 eq715
  have eq1366 (X0 X1 X3 X4 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) ◇ (X0 ◇ X4)) = ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1340 eq721
  have eq1370 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X4)) := superpose eq1340 eq729
  have eq1382 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq1340 eq967
  have eq1389 (X0 X1 X3 X4 : G) : ((((X0 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X4)) = X0 := superpose eq1343 eq1350
  have eq1391 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq939 eq1364
  have eq1393 (X0 X1 X3 X4 : G) : (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) ◇ (X0 ◇ X4)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq939 eq1366
  have eq1398 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq1389 eq1370
  have eq1402 (X0 X1 X4 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X4)) = X0 := superpose eq1398 eq1356
  have eq1406 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (((((X0 ◇ X0) ◇ X3) ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X4)) := superpose eq1398 eq1393
  have eq1410 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq15 eq1406
  have eq1463 (X0 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq1410 eq1391
  have eq1467 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq10 eq1463
  have eq1488 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq1410 eq1382
  have eq1489 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq1343 eq1488
  have eq1490 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1489 eq1467
  have eq1520 (X0 X1 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X4)) = X0 := superpose eq1490 eq1402
  have eq1526 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq1520 eq939
  have eq1548 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4))) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4))) := superpose eq1526 eq446
  have eq1554 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = ((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X5)) := superpose eq1526 eq142
  have eq1555 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = (((((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ ((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) ◇ X0) := superpose eq1526 eq155
  have eq1590 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) ◇ X2) = X0 := superpose eq1526 eq1272
  have eq1826 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1))) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq1526 eq1548
  have eq1827 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4)) := superpose eq1526 eq1826
  have eq1828 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) := superpose eq1526 eq1827
  have eq1829 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq1526 eq1828
  have eq1830 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq1526 eq1829
  have eq1831 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq1526 eq1830
  have eq1832 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq1526 eq1831
  have eq1833 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq1526 eq1832
  have eq1845 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = ((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1526 eq1554
  have eq1846 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq1526 eq1845
  have eq1847 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1526 eq1846
  have eq1848 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) := superpose eq1833 eq1847
  have eq1849 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq1526 eq1848
  have eq1850 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = ((((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X0) := superpose eq1526 eq1555
  have eq1851 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = (((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X0) := superpose eq1526 eq1850
  have eq1852 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = ((((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq1526 eq1851
  have eq1853 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) = ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) := superpose eq1526 eq1852
  have eq1854 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := superpose eq1526 eq1853
  have eq1855 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq1526 eq1854
  have eq1999 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ X2) = X0 := superpose eq1526 eq1590
  have eq2000 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X2) = X0 := superpose eq1526 eq1999
  have eq2001 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq1526 eq2000
  have eq2002 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq2001 eq1855
  have eq2008 (X1 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X3)) = X1 := superpose eq2002 eq1849
  have eq2017 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq2002 eq2008
  have eq2032 (X0 X1 : G) : X0 = X1 := superpose eq2002 eq2017
  have eq2037 (X0 : G) : sK0 ≠ X0 := superpose eq2032 eq9
  subsumption eq2037 eq2032


@[equational_result]
theorem Finite.Equation36524_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : (Y ◇ (((X ◇ Y) ◇ (Y ◇ Z)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((s ◇ Y) ◇ (Y ◇ Z)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((s ◇ Y) ◇ (Y ◇ Z)) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ Y) ◇ (Y ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ Y) ◇ (Y ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ Y) ◇ (Y ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq12 eq12
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq12 eq20
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq14 eq40
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq11
  subsumption eq166 eq90


@[equational_result]
theorem Finite.Equation36638_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ Y) ◇ ((X ◇ (Y ◇ Z)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ (Y ◇ Z)) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ (Y ◇ Z)) ◇ Y)) (fun s => ((Y ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ Y) ◇ (X ◇ Y)) ◇ (Y ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ s) ◇ (Y ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ Y) ◇ s) ◇ (Y ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq23 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq12
  have eq25 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)))) ◇ X0) = X3 := superpose eq9 eq12
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq23
  have eq43 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)))) ◇ X0) = X3 := superpose eq34 eq25
  have eq65 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq34 eq43
  have eq66 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X3 := superpose eq34 eq65
  have eq67 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq34 eq66
  have eq68 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq34 eq67
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq68 eq68
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq10
  subsumption eq71 eq69


@[equational_result]
theorem Finite.Equation36713_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (Y ◇ ((((Y ◇ Y) ◇ Z) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((Y ◇ Y) ◇ Z) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((Y ◇ Y) ◇ Z) ◇ s) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ Y) ◇ Z) ◇ (Y ◇ (X ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ Z) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ Y) ◇ Z) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq9 eq11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = X2 := superpose eq12 eq12
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq15 eq19
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq9 eq29
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq10
  subsumption eq89 eq30


@[equational_result]
theorem Finite.Equation36714_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (Y ◇ ((((Y ◇ Y) ◇ Z) ◇ X) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((Y ◇ Y) ◇ Z) ◇ s) ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((Y ◇ Y) ◇ Z) ◇ s) ◇ Z)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ Y) ◇ Z) ◇ (Y ◇ (X ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Y) ◇ Z) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => (((Y ◇ Y) ◇ Z) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq11
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq15
  have eq35 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) := superpose eq11 eq15
  have eq36 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq15 eq9
  have eq40 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq15 eq11
  have eq43 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq15 eq9
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq33 eq36
  have eq49 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq33 eq48
  have eq50 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq49 eq35
  have eq51 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq49 eq40
  have eq52 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq33 eq51
  have eq53 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq33 eq43
  have eq54 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq53
  have eq55 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq54 eq52
  have eq62 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq54 eq55
  have eq66 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := superpose eq62 eq50
  have eq70 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq62 eq9
  have eq71 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := superpose eq62 eq11
  have eq89 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq62 eq66
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq62 eq70
  have eq110 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq109 eq89
  have eq113 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq110 eq71
  have eq136 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq110 eq113
  have eq137 (X0 X1 : G) : X0 = X1 := superpose eq62 eq136
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq137 eq10
  subsumption eq150 eq137


@[equational_result]
theorem Finite.Equation36867_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation36867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (Y ◇ ((((Y ◇ Z) ◇ Y) ◇ X) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((Y ◇ Z) ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((Y ◇ Z) ◇ Y) ◇ s) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X3) ◇ X1)) = X3 := superpose eq11 eq11
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq11
  have eq35 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq9 eq16
  have eq84 (X0 X2 : G) : X0 = X2 := superpose eq17 eq35
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq10
  subsumption eq151 eq84


@[equational_result]
theorem Finite.Equation37519_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation37519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ (Y ◇ ((X ◇ Y) ◇ Z))) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ (s ◇ Z))) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ (Y ◇ (s ◇ Z))) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X1) := superpose eq8 eq8
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq8 eq10
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X3))) ◇ X0) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X1) := superpose eq10 eq8
  have eq64 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X3))) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq15 eq13
  have eq75 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) ◇ ((X1 ◇ X0) ◇ X4))) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq16 eq16
  have eq81 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq13 eq16
  have eq97 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2))) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) ◇ X0) := superpose eq10 eq16
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq16 eq16
  have eq106 (X0 X1 X2 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X0)) ◇ X1) ◇ X1) = X1 := superpose eq16 eq8
  have eq118 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq16 eq13
  have eq136 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) ◇ X4))) := superpose eq16 eq100
  have eq148 (X0 X1 X3 X4 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X1 ◇ (X0 ◇ X4))) := superpose eq8 eq100
  have eq185 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X4))) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X5))) ◇ X0) := superpose eq100 eq16
  have eq512 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq106 eq13
  have eq515 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X4))) := superpose eq106 eq148
  have eq529 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq106 eq512
  have eq532 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X4))) := superpose eq106 eq515
  have eq551 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5))) = (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ X0) ◇ (X3 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5)))) ◇ X1) := superpose eq16 eq18
  have eq573 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (((X3 ◇ (X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) := superpose eq106 eq18
  have eq642 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq13 eq529
  have eq651 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2))) := superpose eq148 eq529
  have eq667 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq529 eq13
  have eq679 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq529 eq18
  have eq680 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq529 eq11
  have eq698 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq680
  have eq700 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq698 eq642
  have eq701 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (((X3 ◇ (X3 ◇ (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X1)))) ◇ X0) ◇ X3) := superpose eq698 eq573
  have eq703 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq8 eq701
  have eq729 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq703 eq700
  have eq733 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq703 eq667
  have eq734 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq703 eq651
  have eq739 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq703 eq64
  have eq747 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq703 eq81
  have eq752 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq703 eq118
  have eq789 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq703 eq679
  have eq794 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq703 eq729
  have eq801 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq703 eq733
  have eq806 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) ◇ (X1 ◇ X0)) := superpose eq734 eq75
  have eq810 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X4))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq734 eq185
  have eq820 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X4))) := superpose eq734 eq532
  have eq822 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ X1) ◇ X0) := superpose eq734 eq16
  have eq827 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X1) = X1 := superpose eq734 eq106
  have eq833 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X4))) := superpose eq734 eq136
  have eq855 (X0 X1 X3 X4 X5 : G) : (X3 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5))) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5)))) ◇ X1) := superpose eq734 eq551
  have eq867 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq734 eq806
  have eq871 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) ◇ X0) := superpose eq810 eq97
  have eq887 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq822 eq871
  have eq890 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X3)) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq734 eq833
  have eq896 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq734 eq747
  have eq897 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq703 eq896
  have eq899 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq897 eq887
  have eq900 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq897 eq899
  have eq904 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := superpose eq900 eq867
  have eq913 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X3)) := superpose eq904 eq890
  have eq915 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq913 eq801
  have eq918 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq913 eq915
  have eq992 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq918 eq739
  have eq998 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq918 eq794
  have eq1062 (X0 X1 X3 X4 X5 : G) : (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5)) = ((((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5))) ◇ X1) := superpose eq918 eq855
  have eq1230 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq918 eq752
  have eq1231 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq913 eq1230
  have eq1232 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq913 eq1231
  have eq1297 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq918 eq789
  have eq1298 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ X1) ◇ X0) := superpose eq1232 eq1297
  have eq1299 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X4))) := superpose eq1298 eq820
  have eq1301 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq1298 eq827
  have eq1388 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ X0)) := superpose eq900 eq148
  have eq1396 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ X0) := superpose eq918 eq1388
  have eq1401 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq1396 eq992
  have eq1412 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq1401 eq998
  have eq1413 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq1412 eq1299
  have eq1416 (X0 X1 X3 X4 X5 : G) : (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5)) = ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ X1) := superpose eq1412 eq1062
  have eq1574 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X0)) := superpose eq1412 eq1413
  have eq1575 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq1412 eq1574
  have eq1576 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq1301 eq1575
  have eq1577 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1301 eq1576
  have eq1579 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq1577 eq1301
  have eq1591 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq1577 eq1579
  have eq1592 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1577 eq1591
  have eq1602 (X0 X1 X3 X4 X5 : G) : (X3 ◇ ((((X0 ◇ X1) ◇ X4) ◇ X3) ◇ X5)) = X1 := superpose eq1592 eq1416
  have eq1603 (X0 X1 X3 X4 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X4) ◇ X3)) = X1 := superpose eq1577 eq1602
  have eq1604 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X4)) = X1 := superpose eq1577 eq1603
  have eq1605 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X1 := superpose eq1577 eq1604
  have eq1606 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq1577 eq1605
  have eq1607 (X0 X1 : G) : X0 = X1 := superpose eq900 eq1606
  have eq1615 (X0 : G) : sK0 ≠ X0 := superpose eq1607 eq9
  subsumption eq1615 eq1607


@[equational_result]
theorem Finite.Equation38249_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation38249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X Y Z : G) : (Y ◇ ((((X ◇ Y) ◇ Y) ◇ ((X ◇ Y) ◇ Y)) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ s) ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (Y ◇ ((s ◇ s) ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq25
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq12
  subsumption eq92 eq29


@[equational_result]
theorem Finite.Equation38303_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation38303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (Y ◇ ((((X ◇ Y) ◇ Y) ◇ Z) ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ Z) ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (Y ◇ ((s ◇ Z) ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : ((Y ◇ (((X ◇ Y) ◇ Z) ◇ (X ◇ Y))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ ((s ◇ Z) ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ ((s ◇ Z) ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq10 eq31
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq11
  subsumption eq99 eq35


@[equational_result]
theorem Finite.Equation38316_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation38316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ (((X ◇ Y) ◇ Z) ◇ Y)) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ ((s ◇ Z) ◇ Y)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((Y ◇ ((s ◇ Z) ◇ Y)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) ◇ X1) := superpose eq8 eq8
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = ((X1 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0) := superpose eq8 eq10
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq10 eq10
  have eq17 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq8
  have eq23 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq17 eq8
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq17 eq10
  have eq54 (X0 X1 X2 X3 : G) : ((((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) = X0 := superpose eq15 eq10
  have eq70 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X3) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0))) = ((X0 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X3) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) := superpose eq8 eq12
  have eq77 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq17 eq12
  have eq88 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq10
  have eq100 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) := superpose eq12 eq88
  have eq113 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq88 eq10
  have eq119 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq24 eq113
  have eq152 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X1)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq13 eq10
  have eq160 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) = (((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq12 eq119
  have eq162 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))))) = ((((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) := superpose eq15 eq119
  have eq164 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq13 eq119
  have eq185 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X0))) = (((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X0 ◇ X4) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0)))) ◇ X0) := superpose eq15 eq16
  have eq200 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((((X0 ◇ ((X1 ◇ X4) ◇ X0)) ◇ X3) ◇ X5) ◇ X3)) = ((((X0 ◇ ((X1 ◇ X4) ◇ X0)) ◇ X3) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X4) ◇ X0)) ◇ X3))) ◇ (X0 ◇ ((X1 ◇ X4) ◇ X0))) := superpose eq15 eq16
  have eq206 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) = ((X0 ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X3) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq17 eq16
  have eq207 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq12 eq16
  have eq212 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1))) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq13 eq16
  have eq237 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ X2)) ◇ (X1 ◇ X2)) = X1 := superpose eq16 eq10
  have eq261 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))))) := superpose eq16 eq119
  have eq264 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) := superpose eq10 eq206
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0)) := superpose eq10 eq207
  have eq402 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq12 eq264
  have eq416 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq264 eq16
  have eq422 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq264 eq13
  have eq445 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq264 eq17
  have eq547 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = (X3 ◇ (((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ X4) ◇ X3)) := superpose eq12 eq265
  have eq629 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = (X3 ◇ X0) := superpose eq265 eq547
  have eq631 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) = (((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq629 eq160
  have eq633 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0)) := superpose eq629 eq100
  have eq637 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) := superpose eq629 eq402
  have eq649 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) := superpose eq629 eq631
  have eq650 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0))) := superpose eq629 eq649
  have eq651 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0))) = (((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) ◇ X0) ◇ X0) := superpose eq629 eq650
  have eq652 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0))) := superpose eq12 eq651
  have eq655 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq12 eq633
  have eq656 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq629 eq655
  have eq657 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq652 eq656
  have eq661 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X3) ◇ X0))) = (((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ X0) ◇ X0) := superpose eq637 eq185
  have eq665 (X0 X1 X3 : G) : ((((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) = X0 := superpose eq661 eq54
  have eq666 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq665 eq657
  have eq667 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (X1 ◇ X1) := superpose eq666 eq12
  have eq674 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq667 eq416
  have eq676 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) = ((X0 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) := superpose eq667 eq70
  have eq683 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X4) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq667 eq212
  have eq684 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq667 eq152
  have eq687 (X0 X1 X3 X4 X5 : G) : (X3 ◇ ((((X0 ◇ ((X1 ◇ X4) ◇ X0)) ◇ X3) ◇ X5) ◇ X3)) = ((((X0 ◇ ((X1 ◇ X4) ◇ X0)) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X4) ◇ X0)) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X4) ◇ X0))) := superpose eq667 eq200
  have eq692 (X0 X1 X3 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))))) := superpose eq667 eq261
  have eq711 (X0 X1 X3 : G) : ((((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) = ((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0)))) := superpose eq667 eq162
  have eq718 (X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) = ((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq667 eq164
  have eq722 (X0 X1 X2 : G) : ((X2 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X2)) ◇ (X1 ◇ X2)) = X1 := superpose eq667 eq237
  have eq890 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq667 eq676
  have eq899 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq667 eq683
  have eq900 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq667 eq899
  have eq901 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq667 eq684
  have eq905 (X0 X3 X5 : G) : (X3 ◇ ((((X0 ◇ X0) ◇ X3) ◇ X5) ◇ X3)) = ((((X0 ◇ X0) ◇ X3) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq667 eq687
  have eq906 (X0 X3 : G) : (X3 ◇ X3) = ((((X0 ◇ X0) ◇ X3) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq667 eq905
  have eq907 (X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ X1)) := superpose eq906 eq901
  have eq910 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq907 eq422
  have eq911 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq907 eq900
  have eq919 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) = (((((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq667 eq692
  have eq920 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq667 eq919
  have eq921 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq911 eq920
  have eq922 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq23 eq921
  have eq944 (X0 X1 X3 : G) : ((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) = ((((X0 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X0))) := superpose eq667 eq711
  have eq945 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq667 eq944
  have eq946 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq911 eq945
  have eq947 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq23 eq946
  have eq950 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq947 eq911
  have eq951 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq950 eq890
  have eq956 (X0 X3 : G) : (X3 ◇ X3) = ((((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq950 eq906
  have eq983 (X1 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq907 eq718
  have eq984 (X1 : G) : ((X1 ◇ X1) ◇ X1) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq264 eq983
  have eq985 (X1 : G) : ((X1 ◇ X1) ◇ X1) = ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq947 eq984
  have eq986 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq956 eq985
  have eq987 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq986 eq922
  have eq1001 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq986 eq950
  have eq1002 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq986 eq951
  have eq1027 (X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq667 eq722
  have eq1028 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq1027 eq987
  have eq1031 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq1028 eq674
  have eq1033 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq1028 eq1001
  have eq1061 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq1033 eq1002
  have eq1066 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq667 eq1061
  have eq1067 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq1027 eq1066
  have eq1068 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1067 eq910
  have eq1075 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1068 eq1031
  have eq1078 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq1028 eq1075
  have eq1079 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq1028 eq1078
  have eq1080 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1079 eq445
  have eq1083 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq1079 eq17
  have eq1084 (X0 X1 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq1079 eq23
  have eq1086 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq1079 eq77
  have eq1095 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq1079 eq1080
  have eq1096 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq667 eq1095
  have eq1097 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq1028 eq1096
  have eq1098 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq1028 eq1097
  have eq1107 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq1083 eq1084
  have eq1114 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq1107 eq1086
  have eq1115 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq1098 eq1114
  have eq1117 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq1115 eq1083
  have eq1124 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1117 eq1028
  have eq1129 (X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = X1 := superpose eq1124 eq1027
  have eq1139 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq1124 eq1129
  have eq1183 (X0 X2 : G) : X0 = X2 := superpose eq1139 eq1139
  have eq1185 (X0 : G) : sK0 ≠ X0 := superpose eq1183 eq9
  subsumption eq1185 eq1183


@[equational_result]
theorem Finite.Equation38565_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation38565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq14 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X Z Y : G) : ((Z ◇ (((Y ◇ X) ◇ Y) ◇ Y)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ s) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((Y ◇ s) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((Y ◇ s) ◇ Y) ◇ Y)) (fun s => ((Z ◇ s) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq30 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X3) := superpose eq13 eq16
  have eq59 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) ◇ X2) = X1 := superpose eq30 eq16
  have eq66 (X0 X1 X2 X3 : G) : (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X1))) ◇ X2) ◇ X2) = X3 := superpose eq30 eq13
  have eq81 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq59 eq66
  have eq104 (X0 X3 : G) : X0 = X3 := superpose eq13 eq81
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq14
  subsumption eq204 eq104


@[equational_result]
theorem Finite.Equation39126_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation39126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ (((X ◇ Y) ◇ Y) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ s) ◇ (s ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ ((X ◇ Y) ◇ Z)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ (s ◇ Z)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ (s ◇ Z)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq12 eq12
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X1) := superpose eq9 eq12
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq9 eq11
  have eq25 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq9 eq11
  have eq26 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq11 eq12
  have eq39 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X4)) := superpose eq9 eq24
  have eq147 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X1 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X2) ◇ X4)) := superpose eq9 eq39
  have eq151 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X4)) := superpose eq11 eq39
  have eq379 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4)) := superpose eq39 eq151
  have eq478 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))))) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) := superpose eq17 eq17
  have eq511 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) = X0 := superpose eq17 eq9
  have eq985 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq11 eq26
  have eq988 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (((X1 ◇ X0) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq16 eq26
  have eq1042 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq147 eq988
  have eq1071 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ X0) = (X3 ◇ (((X1 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X6)) := superpose eq39 eq379
  have eq1079 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0))) = (X3 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq17 eq379
  have eq1080 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (((X1 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X5)) := superpose eq16 eq379
  have eq1201 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq379 eq1079
  have eq1203 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) = X0 := superpose eq1201 eq511
  have eq1204 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)))) := superpose eq1201 eq478
  have eq1207 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X0) := superpose eq1071 eq1080
  have eq1208 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq1207 eq1042
  have eq1209 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq1207 eq25
  have eq1210 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq1207 eq1204
  have eq1211 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0))) = X0 := superpose eq1207 eq1203
  have eq1215 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq1207 eq985
  have eq1489 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X0))) := superpose eq1207 eq1208
  have eq1490 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) := superpose eq1207 eq1489
  have eq1491 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) := superpose eq1207 eq1490
  have eq1492 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) := superpose eq1207 eq1491
  have eq1493 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) := superpose eq1207 eq1492
  have eq1494 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) := superpose eq1207 eq1493
  have eq1495 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq1207 eq1209
  have eq1496 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq1207 eq1495
  have eq1497 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq1207 eq1496
  have eq1498 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq1207 eq1497
  have eq1499 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)))) := superpose eq1207 eq1210
  have eq1500 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq1207 eq1499
  have eq1501 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq1207 eq1500
  have eq1502 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1207 eq1501
  have eq1503 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1207 eq1502
  have eq1504 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1207 eq1503
  have eq1505 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1207 eq1504
  have eq1506 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1207 eq1505
  have eq1507 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1498 eq1506
  have eq1508 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1498 eq1507
  have eq1509 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1207 eq1508
  have eq1510 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1498 eq1509
  have eq1511 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)))) = X0 := superpose eq1207 eq1211
  have eq1512 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq1207 eq1511
  have eq1513 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq1207 eq1512
  have eq1514 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1207 eq1513
  have eq1515 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1207 eq1514
  have eq1516 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1498 eq1515
  have eq1517 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1498 eq1516
  have eq1518 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1517 eq1510
  have eq1519 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1518 eq1517
  have eq1532 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq1207 eq1215
  have eq1533 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq1207 eq1532
  have eq1534 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq1207 eq1533
  have eq1535 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := superpose eq1519 eq1534
  have eq1536 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ X1) ◇ X0) := superpose eq1207 eq1535
  have eq1537 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X1) ◇ X0) := superpose eq1207 eq1536
  have eq1538 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X0) := superpose eq1207 eq1537
  have eq1539 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) := superpose eq1207 eq1538
  have eq1540 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq1207 eq1539
  have eq1541 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq1519 eq1540
  have eq1542 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq1518 eq1541
  have eq1543 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) := superpose eq1542 eq1494
  have eq1547 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = (X0 ◇ (X0 ◇ X1)) := superpose eq1542 eq1543
  have eq1548 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq1547 eq1542
  have eq1549 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq1207 eq1548
  have eq1550 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq1519 eq1549
  have eq1551 (X0 X1 : G) : X0 = X1 := superpose eq1519 eq1550
  have eq1563 (X0 : G) : sK0 ≠ X0 := superpose eq1551 eq10
  subsumption eq1563 eq1551


@[equational_result]
theorem Finite.Equation39163_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation39163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : (Y ◇ (((X ◇ (Y ◇ Z)) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((s ◇ (Y ◇ Z)) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((s ◇ (Y ◇ Z)) ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ (Y ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Y ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ s) ◇ (Y ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ X0) = X2 := superpose eq13 eq13
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq12 eq13
  have eq35 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq30 eq29
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq13 eq35
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq11
  subsumption eq87 eq37


@[equational_result]
theorem Finite.Equation39214_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation39214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : (Y ◇ (((X ◇ (Z ◇ Z)) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((s ◇ (Z ◇ Z)) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((s ◇ (Z ◇ Z)) ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : ((Y ◇ ((X ◇ Y) ◇ Y)) ◇ (Z ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ (Z ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ s) ◇ (Z ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : (((Y ◇ (X ◇ Y)) ◇ (Z ◇ Z)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ s) ◇ (Z ◇ Z)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ s) ◇ (Z ◇ Z)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1)) = X1 := superpose eq10 eq10
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X2 ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) ◇ (X2 ◇ X2)) := superpose eq10 eq12
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq10 eq12
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) = (((X0 ◇ (X3 ◇ X3)) ◇ X1) ◇ X1) := superpose eq12 eq10
  have eq23 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2))) ◇ (X3 ◇ X3)) = X2 := superpose eq12 eq13
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq12 eq13
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq13 eq12
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq25 eq25
  have eq42 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) ◇ X0) ◇ X0) := superpose eq25 eq10
  have eq72 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq13 eq14
  have eq74 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq25 eq14
  have eq78 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq14 eq14
  have eq92 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq74 eq42
  have eq114 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq92 eq10
  have eq231 (X0 X1 X2 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (X0 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq12 eq114
  have eq267 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq92 eq26
  have eq1217 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))))) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq20 eq18
  have eq3005 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X2) ◇ X1))) ◇ (X3 ◇ X3)) = X1 := superpose eq267 eq13
  have eq3258 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3)) = (((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq20 eq17
  have eq3406 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq17 eq14
  have eq3497 (X0 X1 X2 X4 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq12 eq3258
  have eq3591 (X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) = X1 := superpose eq3406 eq3005
  have eq4824 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1))) := superpose eq13 eq72
  have eq5424 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq28 eq78
  have eq5427 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq25 eq78
  have eq5870 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X3)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X4 ◇ X4)) ◇ (X1 ◇ (X3 ◇ X3)))) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X4 ◇ X4)) ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq72 eq15
  have eq6062 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X3)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq13 eq5870
  have eq6063 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = ((X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq13 eq6062
  have eq6668 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) = ((((X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2)))))) ◇ (X4 ◇ X4)) := superpose eq267 eq23
  have eq6844 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) = ((((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)) := superpose eq3406 eq6668
  have eq6845 (X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) = ((((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X4 ◇ X4)) := superpose eq5427 eq6844
  have eq6846 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) := superpose eq3591 eq6845
  have eq6847 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq6846 eq5424
  have eq6986 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = ((X1 ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X1 ◇ (X3 ◇ X3))) := superpose eq6847 eq6063
  have eq6989 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = ((X1 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X3 ◇ X3))) := superpose eq6847 eq6986
  have eq6990 (X0 X1 X2 X4 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq6989 eq3497
  have eq6992 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2)))) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq6989 eq1217
  have eq6993 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq6989 eq6992
  have eq6994 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq6989 eq6993
  have eq6995 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq6994 eq6990
  have eq6996 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X1 := superpose eq6995 eq6989
  have eq6997 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) := superpose eq6996 eq231
  have eq7411 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq6996 eq6997
  have eq7412 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq6996 eq7411
  have eq7413 (X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) = X1 := superpose eq7412 eq3591
  have eq7415 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) = X0 := superpose eq7412 eq13
  have eq7441 (X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ X3) = X1 := superpose eq7412 eq7413
  have eq7442 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X1 := superpose eq7412 eq7441
  have eq7443 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq7442 eq4824
  have eq7447 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7412 eq7443
  have eq7451 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq7447 eq7415
  have eq7452 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7447 eq7451
  have eq7455 (X0 X3 : G) : X0 = X3 := superpose eq7452 eq7452
  have eq7461 (X0 : G) : sK0 ≠ X0 := superpose eq7455 eq11
  subsumption eq7461 eq7455


@[equational_result]
theorem Finite.Equation39485_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation39485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : (Y ◇ ((((Y ◇ Z) ◇ X) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((Y ◇ Z) ◇ s) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((Y ◇ Z) ◇ s) ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : ((Y ◇ Z) ◇ (Y ◇ ((X ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Z) ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ Z) ◇ (Y ◇ s))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq25 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) = X3 := superpose eq12 eq13
  have eq27 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq13 eq13
  have eq30 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X1 := superpose eq13 eq13
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq25 eq27
  have eq36 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq30 eq35
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X0 := superpose eq36 eq12
  have eq61 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq36 eq38
  have eq62 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq36 eq61
  have eq63 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq36 eq62
  have eq67 (X0 X2 : G) : X0 = X2 := superpose eq63 eq63
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq11
  subsumption eq69 eq67


@[equational_result]
theorem Finite.Equation40037_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ ((X ◇ Z) ◇ Y)) ◇ Z) ◇ (X ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ (s ◇ Y)) ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => (((Y ◇ (s ◇ Y)) ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) = ((((X1 ◇ X0) ◇ X3) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0)) ◇ X3) := superpose eq8 eq8
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0)) := superpose eq8 eq10
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X0) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X3) := superpose eq10 eq8
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq14 eq10
  have eq71 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) := superpose eq15 eq15
  have eq81 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3)))) = X2 := superpose eq15 eq8
  have eq88 (X0 X1 X2 : G) : ((((X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) ◇ X1) = X1 := superpose eq15 eq8
  have eq121 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ X2) = (((X2 ◇ X1) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) := superpose eq14 eq12
  have eq149 (X0 X1 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X3) = ((X4 ◇ (X0 ◇ X4)) ◇ X3) := superpose eq8 eq71
  have eq257 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X3) = ((X4 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) ◇ X4)) ◇ X3) := superpose eq8 eq149
  have eq464 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X3)) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ (((X2 ◇ X1) ◇ X4) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1))) ◇ X4) ◇ ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X3)) ◇ X4)) := superpose eq11 eq13
  have eq481 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X3)) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ (((X2 ◇ X1) ◇ X4) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1))) ◇ X4) ◇ ((X2 ◇ X1) ◇ X4)) := superpose eq257 eq464
  have eq482 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X3)) := superpose eq10 eq481
  have eq508 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X3 ◇ (((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq15 eq482
  have eq521 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) := superpose eq10 eq482
  have eq556 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (X4 ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ X4))) ◇ X2)) ◇ (X4 ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ X4))) = ((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) := superpose eq482 eq15
  have eq570 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = (X2 ◇ (X1 ◇ X2)) := superpose eq8 eq508
  have eq573 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) = ((X2 ◇ (((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq482 eq556
  have eq601 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = (((((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2)) ◇ X3) := superpose eq13 eq16
  have eq672 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq570 eq570
  have eq1208 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X2 ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1))) := superpose eq482 eq36
  have eq1302 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1))) := superpose eq482 eq1208
  have eq1336 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X4))) ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq672 eq521
  have eq1378 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq672 eq521
  have eq1429 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq521 eq8
  have eq1585 (X0 X1 X2 : G) : ((((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq672 eq81
  have eq1587 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X2 ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ X2)) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1))) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq482 eq81
  have eq1646 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1))) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq482 eq1587
  have eq1688 (X0 X1 X2 : G) : ((((X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := superpose eq1429 eq81
  have eq1706 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := superpose eq10 eq1688
  have eq1712 (X0 X1 X2 X3 : G) : (((((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X2) = X2 := superpose eq672 eq88
  have eq1803 (X2 X3 : G) : ((((X3 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq1336 eq1712
  have eq1955 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) := superpose eq1378 eq15
  have eq2134 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = ((((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1378 eq121
  have eq2732 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1706 eq10
  have eq2786 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq2732 eq2134
  have eq3246 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X2 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X2)) ◇ X0) := superpose eq1803 eq71
  have eq3257 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq482 eq3246
  have eq3258 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq3257 eq1429
  have eq3293 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq3258 eq3257
  have eq3307 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq3293 eq1378
  have eq3402 (X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq3307 eq1955
  have eq3424 (X1 X2 : G) : (((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose eq3293 eq3402
  have eq3425 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3424 eq1585
  have eq3431 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq3425 eq2786
  have eq3434 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq3307 eq3431
  have eq3435 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq3434 eq1646
  have eq3436 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) := superpose eq3434 eq1302
  have eq3452 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) := superpose eq3434 eq3436
  have eq3453 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq3452 eq3435
  have eq3455 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) = ((X2 ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq3453 eq573
  have eq3456 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq482 eq3455
  have eq3457 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) := superpose eq3434 eq3456
  have eq3460 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1)) := superpose eq3457 eq3452
  have eq3462 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) := superpose eq3457 eq3460
  have eq3466 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq3462 eq8
  have eq3902 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = (((X2 ◇ X3) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2)) ◇ X3) := superpose eq3466 eq601
  have eq3973 (X2 X3 : G) : (X2 ◇ X2) = (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X3) := superpose eq3466 eq3902
  have eq3974 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X2 := superpose eq3434 eq3973
  have eq3975 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq3466 eq3974
  have eq4291 (X0 X2 : G) : X0 = X2 := superpose eq3975 eq3975
  have eq4293 (X0 : G) : sK0 ≠ X0 := superpose eq4291 eq9
  subsumption eq4293 eq4291


@[equational_result]
theorem Finite.Equation40057_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (((X ◇ Y) ◇ Y) ◇ Z)) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (s ◇ Z)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ (s ◇ Z)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ ((X ◇ Y) ◇ Z)) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ (s ◇ Z)) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ (s ◇ Z)) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = (((X1 ◇ (X0 ◇ X3)) ◇ X0) ◇ X1) := superpose eq9 eq12
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X3)) ◇ X0) ◇ X1) := superpose eq12 eq12
  have eq19 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq9
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq9 eq11
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = ((X1 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq9 eq11
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq12
  have eq37 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq12 eq26
  have eq41 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq12 eq26
  have eq66 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = ((X1 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X4)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) := superpose eq26 eq11
  have eq93 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) = ((((X0 ◇ ((X1 ◇ X2) ◇ X4)) ◇ (X1 ◇ X5)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq26 eq17
  have eq190 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) = ((((X1 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) ◇ X1) ◇ X1) := superpose eq41 eq9
  have eq192 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) = (((X0 ◇ (X0 ◇ X3)) ◇ X0) ◇ X0) := superpose eq41 eq12
  have eq195 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) = ((X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X4)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) := superpose eq41 eq26
  have eq211 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := superpose eq19 eq9
  have eq235 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq22 eq41
  have eq337 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq18 eq11
  have eq350 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X4)) ◇ X2) ◇ (X0 ◇ X5)) ◇ X0) = ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq18 eq26
  have eq372 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2))) := superpose eq235 eq235
  have eq391 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq22 eq235
  have eq410 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq235 eq18
  have eq423 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2))) := superpose eq235 eq372
  have eq424 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2))) := superpose eq235 eq423
  have eq425 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq424 eq410
  have eq426 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = X0 := superpose eq235 eq425
  have eq427 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq426 eq22
  have eq428 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq426 eq192
  have eq445 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq427 eq211
  have eq457 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq428 eq41
  have eq460 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq428 eq190
  have eq462 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ X4)) ◇ (X0 ◇ X0)) := superpose eq428 eq195
  have eq469 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq428 eq337
  have eq487 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq428 eq469
  have eq505 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq487 eq445
  have eq507 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq487 eq391
  have eq530 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq487 eq507
  have eq531 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq457 eq530
  have eq540 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq531 eq505
  have eq545 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq540 eq531
  have eq580 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq545 eq460
  have eq581 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ X4)) ◇ X0) := superpose eq545 eq462
  have eq627 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq581 eq29
  have eq633 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X4)) ◇ (X1 ◇ X5)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq581 eq93
  have eq637 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq581 eq14
  have eq641 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X5)) ◇ X0) := superpose eq581 eq350
  have eq645 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq581 eq37
  have eq657 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X3)) = ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X4)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq581 eq66
  have eq715 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq580 eq627
  have eq716 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq715 eq11
  have eq734 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) = ((((X0 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq581 eq633
  have eq740 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq581 eq641
  have eq741 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq581 eq740
  have eq752 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq715 eq657
  have eq753 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := superpose eq716 eq752
  have eq760 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq753 eq645
  have eq761 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) := superpose eq753 eq741
  have eq765 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq753 eq637
  have eq766 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) = ((((X0 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X1) ◇ X1) ◇ X0) := superpose eq753 eq734
  have eq815 (X0 X1 X2 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X1) ◇ X1) := superpose eq753 eq760
  have eq816 (X0 X1 X2 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) ◇ X1) := superpose eq753 eq815
  have eq817 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ X0) := superpose eq753 eq761
  have eq818 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq816 eq817
  have eq819 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq818 eq816
  have eq823 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq819 eq818
  have eq843 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X1 := superpose eq819 eq765
  have eq844 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq823 eq843
  have eq845 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq545 eq844
  have eq846 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) = (((X0 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X1) ◇ X0) := superpose eq819 eq766
  have eq847 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq823 eq846
  have eq848 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq753 eq847
  have eq849 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq753 eq848
  have eq850 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq819 eq849
  have eq851 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq753 eq850
  have eq852 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq753 eq851
  have eq853 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq819 eq852
  have eq854 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq845 eq853
  have eq860 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq854 eq823
  have eq867 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq854 eq860
  have eq868 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq545 eq867
  have eq1097 (X0 X1 : G) : X0 = X1 := superpose eq854 eq868
  have eq1099 (X0 : G) : sK0 ≠ X0 := superpose eq1097 eq10
  subsumption eq1099 eq1097


@[equational_result]
theorem Finite.Equation40070_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ ((X ◇ Y) ◇ Z)) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ (s ◇ Z)) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ (s ◇ Z)) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X0)) ◇ X1) := superpose eq8 eq8
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0)) := superpose eq8 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = X0 := superpose eq10 eq8
  have eq66 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq13 eq10
  have eq76 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X3)) = ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) := superpose eq10 eq14
  have eq88 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq10 eq14
  have eq102 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq14 eq10
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq66 eq14
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq66 eq10
  have eq134 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq14 eq16
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) := superpose eq16 eq16
  have eq177 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = (((X1 ◇ (((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)))) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq16 eq66
  have eq186 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) = ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq16 eq14
  have eq205 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X0)) ◇ X4)) ◇ (X1 ◇ X0)) := superpose eq16 eq156
  have eq206 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X3)) ◇ X1) := superpose eq10 eq156
  have eq211 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) ◇ X0) := superpose eq14 eq156
  have eq220 (X0 X1 X3 X4 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ (X0 ◇ X4)) ◇ X1) := superpose eq8 eq156
  have eq262 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) ◇ X0)) := superpose eq156 eq14
  have eq266 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) ◇ X0) = (((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X5)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq156 eq16
  have eq306 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq206 eq262
  have eq307 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) := superpose eq88 eq306
  have eq308 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ X1) ◇ X0) = (((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X5)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq307 eq266
  have eq317 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) = (((((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq66 eq17
  have eq353 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = (((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) := superpose eq17 eq14
  have eq357 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = (((X0 ◇ (((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X0) ◇ X4)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X0)) := superpose eq17 eq16
  have eq365 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq10 eq357
  have eq366 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = (((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) := superpose eq365 eq353
  have eq368 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq366
  have eq390 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq13 eq368
  have eq396 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq368
  have eq415 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq368 eq66
  have eq416 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq368 eq13
  have eq444 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X3) ◇ (X0 ◇ X4)) ◇ (X0 ◇ X3))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (((X0 ◇ X3) ◇ (X0 ◇ X4)) ◇ (X0 ◇ X3))) := superpose eq368 eq17
  have eq525 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X4)) ◇ X3) = ((((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ ((((X3 ◇ X1) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) ◇ X5)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) ◇ (((X3 ◇ X1) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1))) := superpose eq11 eq16
  have eq541 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = ((X3 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X4)) ◇ X3) := superpose eq10 eq525
  have eq549 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq541 eq177
  have eq872 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq416 eq416
  have eq888 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq416 eq16
  have eq891 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ X0) := superpose eq416 eq156
  have eq908 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq416 eq220
  have eq913 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq416 eq10
  have eq938 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq416 eq872
  have eq939 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq908 eq127
  have eq940 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) = (((((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq908 eq317
  have eq945 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq908 eq888
  have eq946 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq390 eq940
  have eq949 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq913 eq134
  have eq952 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) ◇ X0) := superpose eq949 eq211
  have eq960 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq952 eq205
  have eq966 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq952 eq891
  have eq977 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) = ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq960 eq186
  have eq979 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq415 eq977
  have eq980 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) := superpose eq979 eq76
  have eq988 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq966 eq120
  have eq997 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq966 eq945
  have eq1000 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq549 eq988
  have eq1002 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) := superpose eq997 eq939
  have eq1023 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq1002 eq946
  have eq1030 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq938 eq1023
  have eq1103 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq1030 eq396
  have eq1131 (X0 X1 X2 : G) : (X0 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq1030 eq913
  have eq1163 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq1000 eq1103
  have eq1166 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq1131 eq102
  have eq1173 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq1166 eq308
  have eq1176 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (((X0 ◇ X3) ◇ (X0 ◇ X4)) ◇ (X0 ◇ X3))) := superpose eq1166 eq444
  have eq1177 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) := superpose eq1166 eq980
  have eq1482 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq1166 eq1173
  have eq1483 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1163 eq1482
  have eq1485 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1483 eq1030
  have eq1515 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X0 ◇ X3)) := superpose eq1483 eq1176
  have eq1516 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) := superpose eq1485 eq1515
  have eq1517 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X1 := superpose eq1483 eq1516
  have eq1522 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq1517 eq1177
  have eq1523 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq1517 eq1522
  have eq1524 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := superpose eq1517 eq1523
  have eq1525 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1517 eq1524
  have eq1700 (X0 X2 : G) : X0 = X2 := superpose eq1525 eq1525
  have eq1702 (X0 : G) : sK0 ≠ X0 := superpose eq1700 eq9
  subsumption eq1702 eq1700


@[equational_result]
theorem Finite.Equation40208_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (Y ◇ Z)) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ (Y ◇ Z)) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => ((Y ◇ (Y ◇ Z)) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ (Y ◇ Z)) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ (Y ◇ Z)) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ (Y ◇ Z)) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X0) ◇ ((X3 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1))) = X3 := superpose eq9 eq11
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = ((X1 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq9 eq11
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) = ((((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X4)) ◇ X3) := superpose eq12 eq18
  have eq32 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X3) := superpose eq11 eq18
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq12 eq18
  have eq53 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X0) := superpose eq18 eq9
  have eq67 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X0) := superpose eq18 eq9
  have eq80 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq37 eq53
  have eq81 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X3) = ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ X3) := superpose eq80 eq31
  have eq88 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) := superpose eq80 eq32
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose eq88 eq67
  have eq99 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq9 eq98
  have eq101 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X3) := superpose eq99 eq81
  have eq105 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X3 := superpose eq99 eq14
  have eq126 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X1 := superpose eq99 eq101
  have eq133 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X3) = X3 := superpose eq126 eq105
  have eq134 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq126 eq133
  have eq135 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq134 eq99
  have eq142 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq134 eq135
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq142 eq142
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq10
  subsumption eq148 eq143


@[equational_result]
theorem Finite.Equation40221_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : (((Y ◇ (Y ◇ Z)) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ (Y ◇ Z)) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => (((Y ◇ (Y ◇ Z)) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X2 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := superpose eq10 eq8
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X2 := superpose eq10 eq14
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := superpose eq10 eq17
  have eq33 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) = X3 := superpose eq19 eq8
  have eq40 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq19 eq20
  have eq43 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq20
  have eq57 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq43 eq8
  have eq74 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X1) = X3 := superpose eq43 eq33
  have eq79 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1)) = X3 := superpose eq43 eq40
  have eq93 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq43 eq43
  have eq99 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq93 eq57
  have eq113 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq99 eq79
  have eq114 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq99 eq74
  have eq118 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq114 eq113
  have eq127 (X0 X2 : G) : X0 = X2 := superpose eq118 eq118
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq9
  subsumption eq129 eq127


@[equational_result]
theorem Finite.Equation40909_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (Y ◇ ((((X ◇ Y) ◇ Y) ◇ Z) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((s ◇ Y) ◇ Y) ◇ Z) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((s ◇ Y) ◇ Y) ◇ Z) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq13 eq11
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq13 eq24
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq12
  subsumption eq84 eq40


@[equational_result]
theorem Finite.Equation40914_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((((Y ◇ (X ◇ Z)) ◇ Y) ◇ Z) ◇ (X ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((((Y ◇ s) ◇ Y) ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => ((((Y ◇ s) ◇ Y) ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) ◇ X0)) ◇ X3) ◇ (X2 ◇ X3)) = X2 := superpose eq8 eq10
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X0) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X3) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq10 eq10
  have eq65 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq14 eq8
  have eq67 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq14 eq10
  have eq68 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ (((X3 ◇ X1) ◇ X3) ◇ X1)) ◇ X2) ◇ X1)) ◇ X1) ◇ (((X3 ◇ X1) ◇ X3) ◇ X1)) := superpose eq14 eq13
  have eq130 (X0 X1 : G) : ((((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq13 eq12
  have eq168 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) := superpose eq8 eq67
  have eq242 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = (((X3 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) := superpose eq15 eq15
  have eq251 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq15 eq8
  have eq274 (X0 X1 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq15 eq65
  have eq280 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) ◇ X1) := superpose eq15 eq14
  have eq285 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq15 eq12
  have eq333 (X0 X1 X2 : G) : ((((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) = (((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq274 eq67
  have eq334 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) = ((((X3 ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq274 eq15
  have eq541 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X0)) ◇ X1) ◇ X0) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X0)) ◇ (X0 ◇ X3)) = X3 := superpose eq8 eq251
  have eq589 (X0 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X3 := superpose eq10 eq541
  have eq644 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq589 eq8
  have eq815 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq644 eq251
  have eq821 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq644 eq8
  have eq855 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq821 eq130
  have eq874 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq855 eq242
  have eq877 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq855 eq15
  have eq880 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq855 eq280
  have eq907 (X0 X2 : G) : ((((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq877 eq333
  have eq910 (X0 X2 : G) : ((((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq874 eq907
  have eq911 (X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq910 eq274
  have eq955 (X1 X2 : G) : ((((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2))) ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq910 eq285
  have eq956 (X0 X1 X3 : G) : ((((X3 ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq910 eq334
  have eq974 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq911 eq880
  have eq975 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose eq974 eq168
  have eq1029 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq8 eq975
  have eq1030 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X1) ◇ X2) ◇ X1)) ◇ X1) ◇ X1) := superpose eq1029 eq68
  have eq1059 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1) ◇ X1) := superpose eq1029 eq1030
  have eq1060 (X1 X3 : G) : ((X3 ◇ X1) ◇ X3) = X1 := superpose eq8 eq1059
  have eq1062 (X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq1060 eq955
  have eq1063 (X0 X1 X3 : G) : ((((X3 ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq1060 eq956
  have eq1076 (X0 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X3) = ((X0 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq1060 eq15
  have eq1475 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq1060 eq1063
  have eq1476 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq1060 eq1475
  have eq1477 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq1476 eq1062
  have eq1478 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq1477 eq1476
  have eq1479 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq1060 eq1478
  have eq1480 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq1479 eq815
  have eq1482 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq1477 eq1480
  have eq1483 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1060 eq1482
  have eq1507 (X0 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X3) = X0 := superpose eq1483 eq1076
  have eq1508 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq1483 eq1507
  have eq1509 (X0 X3 : G) : X0 = X3 := superpose eq1508 eq1508
  have eq1511 (X0 : G) : sK0 ≠ X0 := superpose eq1509 eq9
  subsumption eq1511 eq1509


@[equational_result]
theorem Finite.Equation40917_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (Y ◇ ((((X ◇ Y) ◇ Z) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((s ◇ Y) ◇ Z) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((s ◇ Y) ◇ Z) ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = X2 := superpose eq13 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq12
  subsumption eq82 eq41


@[equational_result]
theorem Finite.Equation40951_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation40951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (Y ◇ ((((X ◇ Z) ◇ Y) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((((s ◇ Z) ◇ Y) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((((s ◇ Z) ◇ Y) ◇ Y) ◇ Y)) (fun s => (Y ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : ((Y ◇ (((X ◇ Y) ◇ Y) ◇ Y)) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ s) ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) (fun s => ((Y ◇ s) ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq13 eq14
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq12
  subsumption eq49 eq38


@[equational_result]
theorem Finite.Equation41082_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation41082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((((Y ◇ Y) ◇ Z) ◇ (X ◇ Z)) ◇ (X ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((((Y ◇ Y) ◇ Z) ◇ s) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => ((((Y ◇ Y) ◇ Z) ◇ s) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq8 eq8
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8
  have eq26 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq10 eq8
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq10 eq11
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq26
  have eq64 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq54
  have eq66 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq64 eq43
  have eq68 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq12 eq66
  have eq70 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq68 eq8
  have eq84 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq68 eq70
  have eq85 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq68 eq84
  have eq108 (X0 X3 : G) : X0 = X3 := superpose eq85 eq85
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq9
  subsumption eq114 eq108


@[equational_result]
theorem Finite.Equation41179_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation41179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : ((Y ◇ Z) ◇ (((X ◇ Y) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Y ◇ Z) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (((s ◇ Y) ◇ Y) ◇ Y)) (fun s => ((Y ◇ Z) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : (((Y ◇ Z) ◇ ((X ◇ Y) ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Z) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (((Y ◇ Z) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X3 := superpose eq12 eq12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X1 := superpose eq13 eq10
  have eq39 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq33 eq18
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq10 eq39
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq11
  subsumption eq102 eq40


@[equational_result]
theorem Finite.Equation41239_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation41239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : (((Y ◇ Z) ◇ Y) ◇ ((X ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (((Y ◇ Z) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => ((s ◇ Y) ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => ((s ◇ Y) ◇ Y)) (fun s => (((Y ◇ Z) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : ((((Y ◇ Z) ◇ Y) ◇ (X ◇ Y)) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((((Y ◇ Z) ◇ Y) ◇ s) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((((Y ◇ Z) ◇ Y) ◇ s) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = (((X1 ◇ X3) ◇ X1) ◇ X0) := superpose eq9 eq11
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq9
  have eq31 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq26 eq11
  have eq66 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq18 eq11
  have eq94 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq31
  have eq111 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq94
  have eq210 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq111
  have eq234 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq111 eq210
  have eq238 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq234 eq31
  have eq256 (X0 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq238 eq66
  have eq257 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq238 eq256
  have eq259 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq257 eq9
  have eq318 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X0 := superpose eq257 eq259
  have eq319 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq257 eq318
  have eq320 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq257 eq319
  have eq329 (X0 X2 : G) : X0 = X2 := superpose eq320 eq320
  have eq331 (X0 : G) : sK0 ≠ X0 := superpose eq329 eq10
  subsumption eq331 eq329


@[equational_result]
theorem Finite.Equation41252_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation41252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((((Y ◇ Z) ◇ Y) ◇ Y) ◇ (X ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((((Y ◇ Z) ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Y)) (fun s => ((((Y ◇ Z) ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq10 eq8
  have eq23 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) := superpose eq8 eq14
  have eq87 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq8 eq17
  have eq88 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq17 eq17
  have eq106 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq87
  have eq113 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = (X0 ◇ X0) := superpose eq17 eq106
  have eq130 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq113 eq88
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq106 eq130
  have eq134 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) := superpose eq131 eq23
  have eq138 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq131 eq16
  have eq140 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq131 eq8
  have eq175 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) := superpose eq131 eq134
  have eq176 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq131 eq175
  have eq177 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = (X1 ◇ X0) := superpose eq106 eq176
  have eq188 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq131 eq138
  have eq189 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq131 eq188
  have eq193 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq177 eq140
  have eq194 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq193 eq131
  have eq195 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq194 eq189
  have eq204 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq194 eq195
  have eq205 (X0 X3 : G) : X0 = X3 := superpose eq204 eq204
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq205 eq9
  subsumption eq207 eq205


@[equational_result]
theorem Finite.Equation41253_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation41253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((((Y ◇ Z) ◇ Y) ◇ Y) ◇ (X ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((((Y ◇ Z) ◇ Y) ◇ Y) ◇ s)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (s ◇ Z)) (fun s => ((((Y ◇ Z) ◇ Y) ◇ Y) ◇ s)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0)) ◇ X3) ◇ X2) = X3 := superpose eq8 eq8
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq10 eq10
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ X3) = ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X0) := superpose eq10 eq10
  have eq17 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq10 eq8
  have eq19 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq10 eq14
  have eq23 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq14 eq10
  have eq24 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq14 eq8
  have eq25 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X0) = ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq14 eq10
  have eq28 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose eq10 eq17
  have eq93 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ X1) ◇ X1) ◇ X0) := superpose eq23 eq10
  have eq163 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq10 eq24
  have eq173 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) = ((((X3 ◇ X0) ◇ X3) ◇ X3) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq24 eq16
  have eq174 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = ((((X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) ◇ X2) ◇ X3) := superpose eq24 eq16
  have eq175 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq10 eq163
  have eq176 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X1 := superpose eq175 eq28
  have eq177 (X0 X1 : G) : (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq175 eq19
  have eq181 (X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) := superpose eq10 eq173
  have eq183 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq93 eq174
  have eq245 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq13 eq16
  have eq277 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq175 eq245
  have eq280 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq277 eq177
  have eq281 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq277 eq176
  have eq307 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) := superpose eq10 eq280
  have eq318 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq280 eq23
  have eq339 (X2 : G) : (X2 ◇ X2) = (X2 ◇ (X2 ◇ X2)) := superpose eq307 eq181
  have eq359 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq339 eq183
  have eq406 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq281 eq318
  have eq407 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq359 eq406
  have eq408 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq407 eq25
  have eq411 (X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq408 eq16
  have eq443 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq411 eq8
  have eq445 (X0 X2 X3 : G) : ((((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) = X3 := superpose eq411 eq11
  have eq540 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq443 eq411
  have eq627 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2) = X3 := superpose eq540 eq445
  have eq628 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = X3 := superpose eq540 eq627
  have eq629 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq540 eq628
  have eq630 (X0 X3 : G) : X0 = X3 := superpose eq629 eq629
  have eq635 (X0 : G) : sK0 ≠ X0 := superpose eq630 eq9
  subsumption eq635 eq630


@[equational_result]
theorem Finite.Equation4916_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation4916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ ((Y ◇ X) ◇ (Y ◇ (Z ◇ Z)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ (Y ◇ (Z ◇ Z))))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (s ◇ (Y ◇ (Z ◇ Z))))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq8 eq8
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq8 eq8
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq10 eq8
  have eq42 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq10 eq11
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq27
  have eq64 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq12 eq56
  have eq65 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq64 eq42
  have eq67 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq12 eq65
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq67 eq8
  have eq85 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq67 eq69
  have eq86 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq67 eq85
  have eq102 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq9
  subsumption eq108 eq102


@[equational_result]
theorem Finite.Equation4952_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation4952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ (Z ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Y ◇ (Z ◇ Y))))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Y ◇ (Z ◇ Y))))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) := superpose eq8 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) = X2 := superpose eq10 eq8
  have eq85 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := superpose eq10 eq17
  have eq96 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose eq8 eq17
  have eq97 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq17 eq17
  have eq108 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq96
  have eq109 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = (X0 ◇ X0) := superpose eq8 eq108
  have eq128 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq109 eq85
  have eq130 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq108 eq128
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq130 eq97
  have eq132 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := superpose eq131 eq8
  have eq133 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq131 eq10
  have eq135 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq131 eq12
  have eq167 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq131 eq132
  have eq168 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq131 eq133
  have eq170 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) = (X0 ◇ (X2 ◇ X1)) := superpose eq131 eq135
  have eq171 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := superpose eq167 eq170
  have eq172 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq171 eq167
  have eq173 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq172 eq131
  have eq176 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq173 eq168
  have eq180 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq173 eq176
  have eq181 (X0 X3 : G) : X0 = X3 := superpose eq180 eq180
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq181 eq9
  subsumption eq183 eq181


@[equational_result]
theorem Finite.Equation4957_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation4957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ (Z ◇ ((Y ◇ X) ◇ Z)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ (s ◇ Z))))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ (Z ◇ (s ◇ Z))))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X0)))) = X2 := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq8 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0))) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X0))) = X2 := superpose eq8 eq10
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2)))))) = X1 := superpose eq12 eq8
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))))) = X1 := superpose eq12 eq10
  have eq85 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (((X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))))))) := superpose eq14 eq11
  have eq152 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = (X0 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq13 eq13
  have eq164 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))))) = X1 := superpose eq13 eq8
  have eq176 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))))) = X0 := superpose eq13 eq47
  have eq181 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq13 eq12
  have eq231 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = (X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X2))) := superpose eq176 eq15
  have eq250 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))))) = X0 := superpose eq14 eq15
  have eq285 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq176 eq48
  have eq521 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1)) ◇ X3))))) = X0 := superpose eq11 eq164
  have eq530 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3))))) = X1 := superpose eq8 eq164
  have eq589 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X1 := superpose eq10 eq530
  have eq640 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := superpose eq589 eq15
  have eq651 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq589 eq8
  have eq815 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) := superpose eq651 eq13
  have eq817 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq651 eq152
  have eq855 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq815 eq817
  have eq856 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq855 eq640
  have eq857 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq856 eq250
  have eq858 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq856 eq85
  have eq874 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq857 eq152
  have eq877 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq857 eq13
  have eq880 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq857 eq181
  have eq908 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq877 eq285
  have eq911 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq874 eq908
  have eq912 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq911 eq176
  have eq974 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq912 eq880
  have eq975 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := superpose eq974 eq181
  have eq1029 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X2))) = X0 := superpose eq975 eq231
  have eq1036 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1)) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1)) ◇ X3))))) = X0 := superpose eq1029 eq521
  have eq1037 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X1)) = X0 := superpose eq10 eq1036
  have eq1038 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1037 eq1029
  have eq1054 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq1038 eq858
  have eq1123 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1054 eq974
  have eq1128 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq1123 eq13
  have eq1493 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := superpose eq1123 eq1128
  have eq1494 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq1123 eq1493
  have eq1495 (X0 X3 : G) : X0 = X3 := superpose eq1494 eq1494
  have eq1500 (X0 : G) : sK0 ≠ X0 := superpose eq1495 eq9
  subsumption eq1500 eq1495


@[equational_result]
theorem Finite.Equation5012_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2))))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (Z ◇ (Z ◇ (Y ◇ Z)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ (Z ◇ (Y ◇ Z))))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Z ◇ (Z ◇ (Y ◇ Z))))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) := superpose eq8 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X3))) ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0))) = X2 := superpose eq10 eq10
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq10
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq8
  have eq23 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq16 eq10
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq16 eq8
  have eq28 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq10 eq17
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ X0)))) = X2 := superpose eq17 eq8
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))))) = X3 := superpose eq12 eq10
  have eq83 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq16 eq23
  have eq103 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X0)))) = X2 := superpose eq83 eq31
  have eq201 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := superpose eq10 eq24
  have eq218 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq201
  have eq219 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) = X1 := superpose eq218 eq28
  have eq294 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)))) := superpose eq15 eq12
  have eq324 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)))) := superpose eq218 eq294
  have eq365 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X3 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3)))) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0))) := superpose eq219 eq12
  have eq393 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0))) := superpose eq324 eq365
  have eq395 (X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) = X2 := superpose eq393 eq103
  have eq415 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq393 eq395
  have eq416 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq415 eq8
  have eq421 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ X0))) = X2 := superpose eq415 eq15
  have eq427 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)))) = X3 := superpose eq415 eq59
  have eq580 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = X3 := superpose eq415 eq427
  have eq581 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq416 eq580
  have eq584 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ X0))) = X2 := superpose eq581 eq421
  have eq586 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq581 eq584
  have eq589 (X0 X3 : G) : X0 = X3 := superpose eq416 eq586
  have eq610 (X0 : G) : sK0 ≠ X0 := superpose eq589 eq9
  subsumption eq610 eq589


@[equational_result]
theorem Finite.Equation5066_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ (Z ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ (Z ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ (Y ◇ (Z ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ ((Y ◇ X) ◇ (Y ◇ (Z ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ (Z ◇ Y))))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (s ◇ (Y ◇ (Z ◇ Y))))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X0 ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq9 eq11
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq9
  have eq31 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq26 eq11
  have eq66 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq16 eq11
  have eq93 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq31
  have eq111 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq93
  have eq207 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq111
  have eq231 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq111 eq207
  have eq233 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq231 eq31
  have eq254 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq233 eq66
  have eq255 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq233 eq254
  have eq256 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := superpose eq255 eq9
  have eq311 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq255 eq256
  have eq312 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq255 eq311
  have eq313 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq255 eq312
  have eq325 (X0 X2 : G) : X0 = X2 := superpose eq313 eq313
  have eq327 (X0 : G) : sK0 ≠ X0 := superpose eq325 eq10
  subsumption eq327 eq325


@[equational_result]
theorem Finite.Equation5093_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ (Z ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Z ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) (fun s => (s ◇ (Z ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Z ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ (Z ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (Y ◇ (s ◇ (Z ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq23 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = X3 := superpose eq12 eq12
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq13 eq10
  have eq39 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq33 eq23
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq10 eq39
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq11
  subsumption eq102 eq40


@[equational_result]
theorem Finite.Equation5107_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X Y Z : G) : ((Y ◇ (Y ◇ (Y ◇ (Z ◇ X)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ (Z ◇ s))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Y ◇ (Z ◇ s))))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X Z Y : G) : (Z ◇ ((Y ◇ (Y ◇ (Y ◇ X))) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Z ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Y ◇ s)))) (fun s => (Z ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq14 eq15
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq13
  subsumption eq50 eq39


@[equational_result]
theorem Finite.Equation5141_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq13 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X Y Z : G) : ((Y ◇ (Y ◇ (Z ◇ (Y ◇ X)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (Z ◇ (Y ◇ s))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (Z ◇ (Y ◇ s))))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X Y Z : G) : (Y ◇ (Z ◇ (Y ◇ ((Y ◇ X) ◇ Y)))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (Z ◇ (Y ◇ (s ◇ Y))))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (Z ◇ (Y ◇ (s ◇ Y))))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq12 eq14
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq23 eq17
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq28
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq12 eq34
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq13
  subsumption eq102 eq40


@[equational_result]
theorem Finite.Equation5295_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := mod_symm (h ..)
  have eq13 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X Y Z : G) : ((Y ◇ (Z ◇ (Y ◇ (Y ◇ X)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Z ◇ (Y ◇ (Y ◇ s))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Z ◇ (Y ◇ (Y ◇ s))))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq12
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq12 eq25
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq13
  subsumption eq101 eq39


@[equational_result]
theorem Finite.Equation5833_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ ((Z ◇ (Y ◇ X)) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ ((Z ◇ s) ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ ((Z ◇ s) ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq8 eq10
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0))) = X0 := superpose eq10 eq8
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) = (X1 ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq10 eq8
  have eq67 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq14 eq14
  have eq112 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq14 eq15
  have eq131 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X1)) := superpose eq10 eq67
  have eq133 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ ((X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq67 eq67
  have eq140 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ ((X4 ◇ X0) ◇ X1)) := superpose eq8 eq67
  have eq213 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) ◇ X0) = ((X0 ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (((X4 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0))) := superpose eq67 eq16
  have eq220 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1))) := superpose eq10 eq16
  have eq247 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) := superpose eq16 eq8
  have eq250 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq16 eq14
  have eq252 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = (X1 ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) := superpose eq16 eq67
  have eq254 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = ((X2 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq16 eq14
  have eq267 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (((X4 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0))) := superpose eq131 eq213
  have eq269 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) ◇ X0) := superpose eq220 eq267
  have eq282 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose eq10 eq140
  have eq418 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)))) := superpose eq17 eq17
  have eq450 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))) = (((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)))) ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X0)) ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))))) := superpose eq17 eq16
  have eq463 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))) = (((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X0)) ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))))) := superpose eq282 eq450
  have eq464 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := superpose eq10 eq463
  have eq507 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq15 eq464
  have eq526 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq464 eq15
  have eq707 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq526 eq16
  have eq709 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) := superpose eq526 eq67
  have eq713 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq526 eq10
  have eq718 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)))) := superpose eq526 eq14
  have eq736 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) := superpose eq713 eq254
  have eq739 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) := superpose eq736 eq252
  have eq749 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq739 eq709
  have eq756 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq749 eq707
  have eq764 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq749 eq756
  have eq765 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq526 eq764
  have eq852 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (((X3 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) := superpose eq464 eq18
  have eq923 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq526 eq765
  have eq933 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq765 eq8
  have eq946 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq765 eq14
  have eq957 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)))) = X0 := superpose eq765 eq464
  have eq990 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq526 eq923
  have eq992 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq990 eq507
  have eq996 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq765 eq992
  have eq1119 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq526 eq933
  have eq1160 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq765 eq1119
  have eq1161 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq996 eq1160
  have eq1170 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq1161 eq112
  have eq1182 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq1161 eq250
  have eq1188 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)))) := superpose eq1161 eq418
  have eq1208 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq1161 eq713
  have eq1212 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq1161 eq718
  have eq1273 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq765 eq1182
  have eq1274 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq1273 eq946
  have eq1275 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq1274 eq957
  have eq1288 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq1274 eq1212
  have eq1289 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq1161 eq1288
  have eq1295 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq1289 eq1208
  have eq1296 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq1275 eq1295
  have eq1302 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq1296 eq765
  have eq1303 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (((X3 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) := superpose eq1296 eq852
  have eq1312 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2) = ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq1296 eq1170
  have eq1327 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = (X0 ◇ (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)))) := superpose eq1296 eq1188
  have eq1379 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) := superpose eq1302 eq1303
  have eq1452 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = (X0 ◇ (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose eq1379 eq1327
  have eq1453 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq464 eq1452
  have eq1454 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X0 := superpose eq1296 eq1453
  have eq1462 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) = X2 := superpose eq1454 eq1312
  have eq1474 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ X0) := superpose eq1462 eq14
  have eq1542 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq1296 eq1474
  have eq1548 (X0 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ ((X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq1542 eq133
  have eq1558 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq1542 eq269
  have eq1639 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := superpose eq1542 eq1548
  have eq1648 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq1558 eq247
  have eq1769 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq1558 eq1648
  have eq1770 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq1558 eq1769
  have eq1771 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq1558 eq1770
  have eq1772 (X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq1558 eq1771
  have eq1773 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq1639 eq1772
  have eq1776 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = X2 := superpose eq1773 eq1558
  have eq1782 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq1773 eq1776
  have eq1783 (X0 X3 : G) : X0 = X3 := superpose eq1782 eq1782
  have eq1788 (X0 : G) : sK0 ≠ X0 := superpose eq1783 eq9
  subsumption eq1788 eq1783


@[equational_result]
theorem Finite.Equation5834_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ ((Z ◇ (Y ◇ X)) ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ ((Z ◇ s) ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ ((Z ◇ s) ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = (X1 ◇ ((X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq8 eq8
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = (X0 ◇ (X1 ◇ ((X3 ◇ X0) ◇ X3))) := superpose eq8 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq8 eq10
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X2) = ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq10 eq10
  have eq71 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq13 eq13
  have eq80 (X0 X1 X2 X3 : G) : ((((X3 ◇ X1) ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)))) = X1 := superpose eq13 eq8
  have eq81 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1))) = X3 := superpose eq13 eq10
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X4 ◇ ((X5 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5))) = (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1))) := superpose eq13 eq12
  have eq88 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)))) = X1 := superpose eq13 eq8
  have eq105 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1)) = ((((X4 ◇ (X1 ◇ X0)) ◇ X4) ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1))) ◇ (((X4 ◇ (X1 ◇ X0)) ◇ X4) ◇ (((X4 ◇ (X1 ◇ X0)) ◇ X4) ◇ X3))) := superpose eq13 eq14
  have eq125 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3))) = (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))))) := superpose eq14 eq13
  have eq149 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X1 ◇ ((X4 ◇ X0) ◇ X4)) := superpose eq8 eq71
  have eq257 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ ((X4 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3)))) ◇ X4)) := superpose eq8 eq149
  have eq271 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) = (X1 ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq13 eq149
  have eq468 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ X3) = ((X4 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ X3)) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X4 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))))) := superpose eq11 eq15
  have eq482 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ X3) = ((X4 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X4 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))))) := superpose eq257 eq468
  have eq483 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) ◇ X3) := superpose eq10 eq482
  have eq508 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))))) ◇ X3) := superpose eq13 eq483
  have eq524 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X1 ◇ X0))) := superpose eq10 eq483
  have eq570 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ X1) := superpose eq8 eq508
  have eq672 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq570 eq570
  have eq1366 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((X3 ◇ X2) ◇ X3) ◇ (((X4 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X4) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq672 eq524
  have eq1378 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq672 eq524
  have eq1426 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq524 eq8
  have eq1433 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq524 eq483
  have eq1689 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2)))) = X0 := superpose eq1426 eq80
  have eq1707 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq1689
  have eq1746 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X3 ◇ X2) ◇ X3))))) = X2 := superpose eq672 eq88
  have eq1806 (X2 X3 : G) : (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) = X2 := superpose eq1366 eq1746
  have eq1892 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq1378 eq13
  have eq2381 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := superpose eq15 eq1433
  have eq2729 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)))) := superpose eq149 eq1707
  have eq3292 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq1806 eq483
  have eq3345 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq3292 eq1378
  have eq3612 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) = (X1 ◇ X1) := superpose eq3345 eq271
  have eq3620 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq3345 eq1892
  have eq3674 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq3345 eq3620
  have eq3678 (X2 : G) : (X2 ◇ (X2 ◇ X2)) = X2 := superpose eq3674 eq1806
  have eq3686 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq3678 eq3292
  have eq3714 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq3686 eq2381
  have eq3723 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq3686 eq3345
  have eq3724 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) = X1 := superpose eq3686 eq3612
  have eq3768 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq3723 eq3714
  have eq3771 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)))) := superpose eq3768 eq2729
  have eq3775 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq3768 eq3724
  have eq3782 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq3775 eq3771
  have eq3794 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3768 eq3782
  have eq3795 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq3768 eq3794
  have eq3796 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq3795 eq8
  have eq3797 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq3795 eq11
  have eq3800 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq3795 eq14
  have eq3818 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) = X3 := superpose eq3795 eq81
  have eq3819 (X0 X1 X3 X4 X5 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X4 ◇ ((X5 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5))) = (((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) := superpose eq3795 eq82
  have eq3828 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) = ((((X4 ◇ (X1 ◇ X0)) ◇ X4) ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) ◇ (((X4 ◇ (X1 ◇ X0)) ◇ X4) ◇ (((X4 ◇ (X1 ◇ X0)) ◇ X4) ◇ X3))) := superpose eq3795 eq105
  have eq3837 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3))) = (X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq3795 eq125
  have eq4737 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) = X3 := superpose eq3795 eq3818
  have eq4741 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X0)) ◇ X5))) = ((X1 ◇ X0) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) := superpose eq3795 eq3819
  have eq4742 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) := superpose eq3795 eq4741
  have eq4757 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) = (((X1 ◇ X0) ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq3795 eq3828
  have eq4758 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) = (((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq4742 eq4757
  have eq4759 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = (X3 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq3800 eq4758
  have eq4760 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X3 := superpose eq4759 eq4737
  have eq4777 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3))) := superpose eq3796 eq3837
  have eq4778 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq3795 eq4777
  have eq4779 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq4760 eq4778
  have eq4782 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq4779 eq3797
  have eq4802 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq4779 eq4782
  have eq4803 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq4779 eq4802
  have eq4804 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq3686 eq4803
  have eq4805 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq4779 eq4804
  have eq4806 (X0 X3 : G) : X0 = X3 := superpose eq4805 eq4805
  have eq4808 (X0 : G) : sK0 ≠ X0 := superpose eq4806 eq9
  subsumption eq4808 eq4806


@[equational_result]
theorem Finite.Equation5837_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (Y ◇ ((Z ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ ((Z ◇ Y) ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (Y ◇ ((Z ◇ Y) ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X2 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) = X2 := superpose eq10 eq8
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq10 eq16
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq10 eq17
  have eq33 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq19 eq8
  have eq38 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = X3 := superpose eq19 eq20
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq10 eq20
  have eq51 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq43 eq8
  have eq72 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) = X3 := superpose eq43 eq33
  have eq77 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq43 eq38
  have eq93 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq43 eq43
  have eq99 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq93 eq51
  have eq112 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq99 eq77
  have eq113 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq99 eq72
  have eq117 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq113 eq112
  have eq126 (X0 X2 : G) : X0 = X2 := superpose eq117 eq117
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq9
  subsumption eq128 eq126


@[equational_result]
theorem Finite.Equation5947_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (Y ◇ X)) ◇ ((Z ◇ (Y ◇ (Y ◇ X))) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Z ◇ s) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ ((Z ◇ s) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ ((Y ◇ X) ◇ ((Z ◇ (Y ◇ X)) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ ((Z ◇ s) ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (s ◇ ((Z ◇ s) ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X1))) := superpose eq12 eq12
  have eq24 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq11 eq11
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X1)) = (X0 ◇ ((X3 ◇ X0) ◇ X1)) := superpose eq9 eq11
  have eq26 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq9 eq11
  have eq41 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq12 eq25
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X2) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X4 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X0)) := superpose eq25 eq11
  have eq192 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X0))) := superpose eq41 eq12
  have eq239 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X1 := superpose eq26 eq12
  have eq241 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X1 := superpose eq26 eq41
  have eq338 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0)) := superpose eq16 eq11
  have eq387 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq239 eq12
  have eq388 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq239 eq9
  have eq395 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X2)) = (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq239 eq25
  have eq397 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))))) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose eq239 eq26
  have eq409 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose eq239 eq397
  have eq519 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))))) := superpose eq241 eq241
  have eq539 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X0)) = ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq241 eq11
  have eq543 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X4 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) := superpose eq241 eq16
  have eq562 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))))) := superpose eq241 eq519
  have eq563 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)) := superpose eq241 eq562
  have eq564 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0))) := superpose eq563 eq543
  have eq565 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X0)) = X0 := superpose eq241 eq564
  have eq567 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq565 eq192
  have eq602 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) := superpose eq567 eq539
  have eq603 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq567 eq338
  have eq622 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq602 eq239
  have eq624 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq602 eq387
  have eq625 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq602 eq388
  have eq627 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq602 eq395
  have eq630 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq602 eq409
  have eq646 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq622 eq624
  have eq660 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq567 eq603
  have eq661 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq660 eq630
  have eq662 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq660 eq646
  have eq711 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq660 eq662
  have eq721 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq711 eq661
  have eq726 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq721 eq711
  have eq730 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq726 eq625
  have eq732 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq726 eq627
  have eq877 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X2) = ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X4 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) := superpose eq732 eq64
  have eq928 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq11 eq877
  have eq929 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq928 eq11
  have eq930 (X0 X1 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq928 eq24
  have eq959 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq928 eq929
  have eq960 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq928 eq959
  have eq961 (X0 X1 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ X0) ◇ X1) := superpose eq928 eq930
  have eq962 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq928 eq961
  have eq963 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq928 eq962
  have eq964 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq928 eq963
  have eq965 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq928 eq964
  have eq966 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq928 eq965
  have eq967 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq726 eq966
  have eq968 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq730 eq967
  have eq970 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq968 eq960
  have eq973 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq968 eq970
  have eq974 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq968 eq973
  have eq1264 (X0 X1 : G) : X0 = X1 := superpose eq974 eq968
  have eq1266 (X0 : G) : sK0 ≠ X0 := superpose eq1264 eq10
  subsumption eq1266 eq1264


@[equational_result]
theorem Finite.Equation5951_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (Y ◇ X)) ◇ ((Z ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Z ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => (s ◇ ((Z ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (Y ◇ ((Y ◇ X) ◇ ((Z ◇ Y) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ (s ◇ ((Z ◇ Y) ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ (s ◇ ((Z ◇ Y) ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X1) ◇ X1)) = (X0 ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq9 eq11
  have eq24 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq12 eq12
  have eq31 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X4 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X2))) ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X2)))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X2)))) := superpose eq12 eq16
  have eq34 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X2) ◇ X2))) = (X1 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq11 eq16
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq12 eq16
  have eq54 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq16 eq9
  have eq68 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq16 eq9
  have eq80 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = (X3 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq37 eq54
  have eq81 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X4 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2)))) = (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2)))) := superpose eq80 eq31
  have eq84 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq80 eq24
  have eq89 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2))) = (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) := superpose eq80 eq34
  have eq99 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq89 eq68
  have eq100 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq99
  have eq102 (X0 X1 X2 X4 : G) : (X1 ◇ ((X4 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq100 eq81
  have eq105 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq100 eq84
  have eq127 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X2 := superpose eq100 eq102
  have eq132 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq127 eq105
  have eq144 (X0 X2 : G) : X0 = X2 := superpose eq132 eq132
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq10
  subsumption eq146 eq144


@[equational_result]
theorem Finite.Equation6820_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation6820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : ((Y ◇ (Y ◇ (X ◇ (Z ◇ Y)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (s ◇ (Z ◇ Y))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (s ◇ (Z ◇ Y))))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : (((Y ◇ (Y ◇ X)) ◇ Y) ◇ (Z ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Z ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((s ◇ Y) ◇ (Z ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq13 eq13
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X1 := superpose eq13 eq13
  have eq30 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X2 := superpose eq12 eq13
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq30 eq25
  have eq36 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq27 eq35
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq36 eq30
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq11
  subsumption eq61 eq56


@[equational_result]
theorem Finite.Equation6878_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation6878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Z Y : G) : ((Z ◇ (Y ◇ (Y ◇ X))) ◇ ((Y ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ s) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Z ◇ s) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Y Z : G) : (Y ◇ ((Z ◇ (Y ◇ X)) ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Z ◇ s) ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Z ◇ s) ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq13 eq13
  have eq26 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq12
  have eq31 (X0 X1 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ (((X3 ◇ (X3 ◇ X0)) ◇ X3) ◇ X1)))) := superpose eq12 eq10
  have eq45 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = ((X4 ◇ X2) ◇ X0) := superpose eq10 eq26
  have eq152 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X3) := superpose eq12 eq45
  have eq254 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = ((X4 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0))))) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq12 eq19
  have eq277 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq12 eq19
  have eq380 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) := superpose eq45 eq152
  have eq401 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq152 eq12
  have eq413 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X4 ◇ X0)) ◇ X4)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ (X4 ◇ X0)) ◇ X4))) ◇ (X0 ◇ X1)))) := superpose eq152 eq10
  have eq816 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ X3) = ((X4 ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X6 ◇ X1))) ◇ X3) := superpose eq45 eq380
  have eq837 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ X3) = ((X4 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X5 ◇ X2))) ◇ X3) := superpose eq19 eq380
  have eq947 (X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ X1) ◇ X3) := superpose eq816 eq837
  have eq954 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ (((X3 ◇ X0) ◇ X3) ◇ X1)))) := superpose eq947 eq31
  have eq957 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) := superpose eq947 eq152
  have eq958 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = ((X4 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0))))) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq947 eq254
  have eq959 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq947 eq277
  have eq965 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq947 eq401
  have eq966 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X0) ◇ X4)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X4))) ◇ (X0 ◇ X1)))) := superpose eq947 eq413
  have eq1175 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))) := superpose eq947 eq954
  have eq1176 (X0 X1 X3 : G) : (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))) := superpose eq947 eq1175
  have eq1188 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq947 eq957
  have eq1189 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = ((X4 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0))))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1188 eq958
  have eq1190 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1188 eq1189
  have eq1191 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq947 eq1190
  have eq1192 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0)) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq947 eq1191
  have eq1193 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq1188 eq1192
  have eq1194 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq947 eq1193
  have eq1196 (X0 X1 X3 : G) : (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq1194 eq1176
  have eq1199 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq947 eq959
  have eq1200 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq1196 eq1199
  have eq1201 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq947 eq1200
  have eq1221 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq1194 eq965
  have eq1222 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq1188 eq1221
  have eq1223 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq947 eq1222
  have eq1224 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X0) ◇ X4)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ X0) ◇ X4))) ◇ X0))) := superpose eq1194 eq966
  have eq1225 (X0 X1 X3 X4 : G) : (X3 ◇ ((X4 ◇ X0) ◇ X4)) = (X1 ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq1188 eq1224
  have eq1226 (X0 X3 X4 : G) : (X3 ◇ X0) = (X3 ◇ ((X4 ◇ X0) ◇ X4)) := superpose eq1196 eq1225
  have eq1227 (X0 X3 X4 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X4)) := superpose eq947 eq1226
  have eq1228 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq1227 eq1223
  have eq1230 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq1227 eq1201
  have eq1242 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := superpose eq1227 eq1228
  have eq1243 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq1227 eq1242
  have eq1244 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq1227 eq1230
  have eq1245 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1243 eq1244
  have eq1248 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = X0 := superpose eq1245 eq1227
  have eq1252 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq1245 eq1248
  have eq1253 (X0 X3 : G) : X0 = X3 := superpose eq1252 eq1252
  have eq1258 (X0 : G) : sK0 ≠ X0 := superpose eq1253 eq11
  subsumption eq1258 eq1253


@[equational_result]
theorem Finite.Equation6895_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation6895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : ((Y ◇ (Y ◇ ((Z ◇ Y) ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ ((Z ◇ Y) ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ ((Z ◇ Y) ◇ s)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1)))) ◇ X0))) = X1 := superpose eq11 eq11
  have eq19 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X1) = X3 := superpose eq13 eq13
  have eq41 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq11 eq19
  have eq50 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = (X1 ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq19 eq11
  have eq52 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq41 eq11
  have eq54 (X0 X1 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0))) = X1 := superpose eq41 eq17
  have eq68 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq52 eq52
  have eq69 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq13 eq52
  have eq70 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := superpose eq19 eq52
  have eq72 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq52 eq13
  have eq81 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))) = X1 := superpose eq68 eq54
  have eq83 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := superpose eq69 eq81
  have eq87 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq69 eq50
  have eq91 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := superpose eq70 eq68
  have eq92 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) = X1 := superpose eq91 eq83
  have eq95 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq72 eq92
  have eq100 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq72 eq95
  have eq101 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X0))) = X1 := superpose eq100 eq87
  have eq104 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq101 eq19
  have eq122 (X0 X2 : G) : X0 = X2 := superpose eq104 eq104
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq12
  subsumption eq127 eq122


@[equational_result]
theorem Finite.Equation6912_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation6912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : ((Y ◇ (Y ◇ ((Z ◇ Z) ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ ((Z ◇ Z) ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ ((Z ◇ Z) ◇ s)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Z Y : G) : ((Z ◇ Z) ◇ ((Y ◇ (Y ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ Z) ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Z ◇ Z) ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X Y Z : G) : (Y ◇ ((Z ◇ Z) ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((Z ◇ Z) ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((Z ◇ Z) ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X3) ◇ X0))) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2))) = ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq11 eq14
  have eq24 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq14 eq14
  have eq26 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq13 eq14
  have eq27 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X3 ◇ (X3 ◇ X0)) ◇ X3) := superpose eq14 eq13
  have eq48 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq26 eq11
  have eq76 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq14 eq15
  have eq77 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq26 eq15
  have eq81 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq15 eq15
  have eq93 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq77 eq48
  have eq110 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq93 eq14
  have eq113 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq93 eq11
  have eq247 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq113 eq14
  have eq260 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq93 eq27
  have eq2890 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq15 eq260
  have eq4901 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1) = (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1) ◇ X0) := superpose eq14 eq76
  have eq5459 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = ((X3 ◇ X3) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq81 eq22
  have eq6004 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))))) = X1 := superpose eq81 eq16
  have eq6375 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((((X2 ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) := superpose eq24 eq247
  have eq6577 (X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X1 := superpose eq14 eq6375
  have eq6581 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq6577 eq2890
  have eq6592 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = ((X3 ◇ X3) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq6581 eq5459
  have eq6594 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = X1 := superpose eq110 eq6592
  have eq6595 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))))) = X1 := superpose eq6594 eq6004
  have eq6597 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq6594 eq6595
  have eq6598 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := superpose eq6597 eq11
  have eq6599 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := superpose eq6597 eq13
  have eq7155 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq6599 eq4901
  have eq7159 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := superpose eq7155 eq6598
  have eq7166 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7155 eq7159
  have eq7170 (X0 X2 : G) : X0 = X2 := superpose eq7166 eq7166
  have eq7178 (X0 : G) : sK0 ≠ X0 := superpose eq7170 eq12
  subsumption eq7178 eq7170


@[equational_result]
theorem Finite.Equation7587_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation7587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ ((Y ◇ (Z ◇ (Y ◇ X))) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ ((Y ◇ (Z ◇ s)) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ ((Y ◇ (Z ◇ s)) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq8 eq8
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = (X0 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) := superpose eq8 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq10 eq8
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq17 eq10
  have eq53 (X0 X1 X2 X3 : G) : (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X3 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := superpose eq13 eq10
  have eq83 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) = (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)))) := superpose eq13 eq12
  have eq88 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0)) = X0 := superpose eq12 eq10
  have eq93 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) = (X3 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3))) := superpose eq12 eq8
  have eq98 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)))) := superpose eq8 eq88
  have eq129 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X3 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ ((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X1)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1))) := superpose eq13 eq14
  have eq154 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ X0) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq12 eq14
  have eq198 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) ◇ X0) := superpose eq10 eq154
  have eq282 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) = ((X3 ◇ (X4 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3))) ◇ X3) := superpose eq12 eq198
  have eq338 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) := superpose eq198 eq282
  have eq345 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3))) := superpose eq338 eq93
  have eq350 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq8 eq345
  have eq351 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq350 eq12
  have eq359 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq351 eq8
  have eq365 (X0 X1 X3 : G) : (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := superpose eq351 eq53
  have eq374 (X0 X1 X3 X4 : G) : ((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) = (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq351 eq83
  have eq376 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq351 eq98
  have eq378 (X0 X1 X3 X4 : G) : (X1 ◇ ((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X1)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1))) = (((X1 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq351 eq129
  have eq481 (X0 X1 X3 : G) : (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := superpose eq351 eq365
  have eq482 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := superpose eq351 eq481
  have eq490 (X0 X1 X3 : G) : (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) = (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ ((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq351 eq374
  have eq491 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq351 eq490
  have eq494 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq351 eq376
  have eq497 (X0 X1 X3 X4 : G) : (X1 ◇ ((((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X4 ◇ X1)) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1))) = ((X1 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq351 eq378
  have eq498 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ (((X1 ◇ (X3 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1))) := superpose eq351 eq497
  have eq499 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X0))) = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq351 eq498
  have eq500 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X1 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq359 eq499
  have eq501 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq500 eq482
  have eq502 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq500 eq494
  have eq504 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := superpose eq501 eq491
  have eq505 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq359 eq504
  have eq506 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq505 eq22
  have eq512 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq505 eq502
  have eq513 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq512 eq359
  have eq521 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq513 eq506
  have eq535 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq513 eq521
  have eq803 (X0 X1 : G) : X0 = X1 := superpose eq513 eq535
  have eq808 (X0 : G) : sK0 ≠ X0 := superpose eq803 eq9
  subsumption eq808 eq803


@[equational_result]
theorem Finite.Equation7701_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation7701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : (((Y ◇ (Y ◇ X)) ◇ (Z ◇ (Y ◇ (Y ◇ X)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ (Z ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((s ◇ (Z ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq14 (X Y Z : G) : (Y ◇ (((Y ◇ X) ◇ (Z ◇ (Y ◇ X))) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Y ◇ ((s ◇ (Z ◇ s)) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (Y ◇ ((s ◇ (Z ◇ s)) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq14 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq10 eq31
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq11
  subsumption eq99 eq35


@[equational_result]
theorem Finite.Equation7755_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation7755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq14 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X Z Y : G) : ((Z ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ (Y ◇ X)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ (s ◇ s)) ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ s))) (fun s => ((Z ◇ (s ◇ s)) ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq17 eq17
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq13 eq27
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq14
  subsumption eq94 eq31


@[equational_result]
theorem Finite.Equation7763_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation7763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq14 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X Z Y : G) : (Z ◇ ((Y ◇ (Y ◇ (X ◇ Y))) ◇ Z)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (Z ◇ (s ◇ Z))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (Y ◇ (s ◇ Y)))) (fun s => (Z ◇ (s ◇ Z))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq30 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ X3)) := superpose eq13 eq16
  have eq59 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = X1 := superpose eq30 eq16
  have eq66 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2))) = X3 := superpose eq30 eq13
  have eq81 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq59 eq66
  have eq104 (X0 X3 : G) : X0 = X3 := superpose eq13 eq81
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq14
  subsumption eq204 eq104


@[equational_result]
theorem Finite.Equation8485_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation8485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq8 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq9 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X Y Z : G) : ((Y ◇ X) ◇ (((Z ◇ (Y ◇ X)) ◇ Y) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (((Z ◇ s) ◇ Y) ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => (s ◇ (((Z ◇ s) ◇ Y) ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = (X1 ◇ ((X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq8 eq8
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (X0 ◇ (((X3 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq8 eq10
  have eq16 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X2 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) ◇ (X0 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2)))) = X0 := superpose eq10 eq8
  have eq18 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3) = (X1 ◇ ((((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq10 eq8
  have eq74 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = (((X3 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) := superpose eq14 eq14
  have eq82 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2))) = X2 := superpose eq14 eq8
  have eq127 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose eq15 eq10
  have eq139 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (((X3 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq10 eq74
  have eq140 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (((X3 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq15 eq74
  have eq144 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq74
  have eq148 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (((X4 ◇ X0) ◇ X2) ◇ X2) := superpose eq8 eq74
  have eq230 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose eq15 eq17
  have eq245 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)) = ((X0 ◇ (X0 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3))) ◇ (((X4 ◇ (X0 ◇ (X0 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)))) ◇ X0) ◇ X0)) := superpose eq17 eq14
  have eq251 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)) = (X0 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X3)) := superpose eq10 eq245
  have eq274 (X0 X1 X2 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2) = (((X4 ◇ X2) ◇ X2) ◇ X2) := superpose eq14 eq148
  have eq470 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq10 eq82
  have eq508 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (((X4 ◇ (X0 ◇ ((X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0))) ◇ X3) ◇ X3) := superpose eq82 eq148
  have eq514 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)))) = ((X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1))))) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq82 eq15
  have eq531 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq82 eq514
  have eq555 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = (X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) ◇ X3) ◇ X3))) := superpose eq82 eq18
  have eq653 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq148 eq531
  have eq662 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq531 eq11
  have eq700 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) := superpose eq15 eq662
  have eq702 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = (X3 ◇ (X0 ◇ ((((X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) ◇ X3) ◇ X3))) := superpose eq700 eq555
  have eq704 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq8 eq702
  have eq720 (X0 X1 X2 : G) : (X1 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose eq704 eq127
  have eq727 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (((X3 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq704 eq140
  have eq728 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq704 eq144
  have eq732 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq704 eq230
  have eq758 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq704 eq653
  have eq790 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq704 eq728
  have eq791 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq790 eq470
  have eq793 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq704 eq732
  have eq797 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq758 eq727
  have eq799 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq758 eq14
  have eq816 (X0 X2 X4 : G) : (((X4 ◇ X2) ◇ X2) ◇ X2) = ((X0 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq758 eq274
  have eq831 (X0 X1 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (((X4 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X3) ◇ X3) := superpose eq758 eq508
  have eq870 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq797 eq720
  have eq873 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq870 eq793
  have eq875 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq870 eq791
  have eq877 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq873 eq790
  have eq887 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq873 eq875
  have eq890 (X0 X1 X2 : G) : ((X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) := superpose eq799 eq139
  have eq893 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) ◇ (X2 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2))) = X2 := superpose eq890 eq16
  have eq912 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = X2 := superpose eq877 eq816
  have eq922 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (((X4 ◇ (X0 ◇ X0)) ◇ X3) ◇ X3) := superpose eq912 eq831
  have eq923 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (((X4 ◇ X0) ◇ X3) ◇ X3) := superpose eq873 eq922
  have eq924 (X0 X1 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = X0 := superpose eq923 eq10
  have eq932 (X0 X1 X3 : G) : (X0 ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) = (((X1 ◇ X0) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) := superpose eq923 eq251
  have eq968 (X0 X2 : G) : ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ (X2 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) = X2 := superpose eq923 eq893
  have eq1049 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq923 eq924
  have eq1056 (X0 X1 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = (((X1 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3)) ◇ ((X0 ◇ X3) ◇ X3)) := superpose eq923 eq932
  have eq1123 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) = X2 := superpose eq923 eq968
  have eq1124 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq1123 eq887
  have eq1125 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq877 eq1124
  have eq1126 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq1125 eq799
  have eq1139 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq1125 eq1049
  have eq1144 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ X3) ◇ X3) := superpose eq1125 eq1056
  have eq1186 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq1125 eq1144
  have eq1189 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq1186 eq1126
  have eq1190 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1186 eq1139
  have eq1207 (X0 X1 : G) : X0 = X1 := superpose eq1190 eq1189
  have eq1212 (X0 : G) : sK0 ≠ X0 := superpose eq1207 eq9
  subsumption eq1212 eq1207


@[equational_result]
theorem Finite.Equation9337_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ (Y ◇ (Z ◇ Y)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ (Z ◇ Y))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Y ◇ (Z ◇ Y))))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X2 := superpose eq11 eq11
  have eq17 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq11
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq9 eq16
  have eq84 (X0 X1 : G) : X0 = X1 := superpose eq17 eq35
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq10
  subsumption eq145 eq84


@[equational_result]
theorem Finite.Equation9345_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ (Z ◇ (Y ◇ Y)))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Z ◇ (Y ◇ Y))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Z ◇ (Y ◇ Y))))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ Y) ◇ (Z ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Y) ◇ (Z ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Y) ◇ (Z ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq11
  have eq24 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq12 eq12
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq24
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq9 eq30
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq10
  subsumption eq90 eq31


@[equational_result]
theorem Finite.Equation9384_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Y Z : G) : ((Y ◇ (X ◇ (Y ◇ (Z ◇ Z)))) ◇ Z) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Z)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ (s ◇ (Y ◇ (Z ◇ Z))))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ (s ◇ (Y ◇ (Z ◇ Z))))) (fun s => (s ◇ Z)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X Y Z : G) : (((Y ◇ X) ◇ Z) ◇ (Y ◇ (Z ◇ Z))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((s ◇ Z) ◇ (Y ◇ (Z ◇ Z)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((s ◇ Z) ◇ (Y ◇ (Z ◇ Z)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq9 eq11
  have eq26 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) = X2 := superpose eq12 eq11
  have eq34 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq15
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2))) := superpose eq15 eq12
  have eq43 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq15 eq9
  have eq53 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq34 eq43
  have eq54 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq9 eq53
  have eq55 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq54 eq42
  have eq62 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq55
  have eq63 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := superpose eq62 eq9
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := superpose eq62 eq11
  have eq75 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq62 eq26
  have eq94 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq54 eq75
  have eq112 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq63 eq64
  have eq117 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq54 eq112
  have eq119 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq117 eq94
  have eq122 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq119 eq64
  have eq146 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq119 eq122
  have eq147 (X0 X1 : G) : X0 = X1 := superpose eq62 eq146
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq10
  subsumption eq155 eq147


@[equational_result]
theorem Finite.Equation9603_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq10 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X Z Y : G) : ((Z ◇ (Y ◇ X)) ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ s) ◇ (Y ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Z ◇ s) ◇ (Y ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (((X3 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1)))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X2 ◇ X0) ◇ (((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X0)))) := superpose eq9 eq11
  have eq15 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ (X2 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2))) := superpose eq11 eq11
  have eq16 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq9 eq11
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X0))) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) := superpose eq11 eq11
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) := superpose eq11 eq9
  have eq20 (X0 X1 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X3)) = (X1 ◇ (X0 ◇ (X1 ◇ ((X3 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X1)))) := superpose eq11 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ (((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) = (X0 ◇ (X3 ◇ (((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq9 eq16
  have eq47 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) = ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq16 eq16
  have eq54 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))))) = X1 := superpose eq16 eq11
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := superpose eq16 eq9
  have eq61 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) = ((X2 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X1) ◇ (((X3 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)))) := superpose eq16 eq15
  have eq84 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = (((X3 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) ◇ (X2 ◇ (((X3 ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) ◇ X0))) := superpose eq9 eq20
  have eq142 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = (X1 ◇ ((X3 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)))) := superpose eq16 eq14
  have eq156 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1))) := superpose eq14 eq15
  have eq181 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X3 ◇ ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1)))) ◇ ((X4 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq14 eq17
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))))) := superpose eq16 eq17
  have eq207 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))))) = X1 := superpose eq17 eq11
  have eq360 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) = ((X4 ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq142 eq17
  have eq476 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X4 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))))))) := superpose eq56 eq207
  have eq531 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) ◇ X0) = (X4 ◇ ((X3 ◇ X0) ◇ (X4 ◇ ((((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) ◇ X0) ◇ X4)))) := superpose eq207 eq20
  have eq565 (X0 X1 X2 X4 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X4 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X4 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))))))) := superpose eq29 eq476
  have eq603 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq56 eq18
  have eq609 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = ((X2 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq18
  have eq625 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))))) := superpose eq18 eq11
  have eq634 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X3))) = ((X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (X3 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X3))) := superpose eq18 eq16
  have eq646 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X4 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X5 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X5 ◇ (X0 ◇ X1)))))) := superpose eq18 eq207
  have eq650 (X0 X1 X2 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X5 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X5 ◇ (X0 ◇ X1)))))) := superpose eq634 eq646
  have eq721 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = ((X3 ◇ X1) ◇ ((X4 ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) ◇ (X1 ◇ (X4 ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))))) := superpose eq47 eq17
  have eq726 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) = (((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X2 ◇ (((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))))))) := superpose eq47 eq12
  have eq728 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = ((X3 ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq47 eq17
  have eq865 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1))) := superpose eq18 eq19
  have eq880 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) = (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2))) := superpose eq19 eq19
  have eq914 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = ((X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq19 eq17
  have eq945 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) := superpose eq865 eq880
  have eq946 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq945 eq19
  have eq957 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = ((X2 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq946 eq609
  have eq995 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq634 eq914
  have eq996 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq945 eq995
  have eq1046 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))) = (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq18 eq946
  have eq1048 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X0))) = (((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X0))) := superpose eq11 eq946
  have eq1057 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq946 eq946
  have eq1090 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = (X2 ◇ ((X3 ◇ X2) ◇ (((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X2)))) := superpose eq946 eq14
  have eq1091 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2))) := superpose eq946 eq15
  have eq1096 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X4 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X4 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))))) := superpose eq946 eq17
  have eq1200 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq946 eq1046
  have eq1213 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq1057
  have eq1237 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) = ((X4 ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq1213 eq360
  have eq1251 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq625 eq1096
  have eq1252 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2))) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X2) := superpose eq1251 eq1091
  have eq1263 (X0 X1 X2 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X5 ◇ (X0 ◇ X1)))) := superpose eq1252 eq650
  have eq1264 (X0 X1 X2 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X5 ◇ (X0 ◇ X1)))) := superpose eq1213 eq1263
  have eq1265 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) = ((X4 ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq1264 eq1237
  have eq1268 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = ((X1 ◇ X2) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2)) := superpose eq1264 eq996
  have eq1270 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq1264 eq1200
  have eq1275 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) := superpose eq1268 eq625
  have eq1278 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq1270 eq957
  have eq1282 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X0)) = (X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X0))) := superpose eq1278 eq1048
  have eq1296 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (X2 ◇ ((X3 ◇ X2) ◇ (((X3 ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2)))) := superpose eq1282 eq1090
  have eq1332 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (X2 ◇ ((X3 ◇ X2) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X2)))) := superpose eq1282 eq1296
  have eq1333 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose eq1251 eq1332
  have eq1339 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq1333 eq1275
  have eq1348 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ (((X2 ◇ X1) ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1))) := superpose eq1333 eq1265
  have eq1393 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) = ((X2 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2))) := superpose eq1348 eq61
  have eq1394 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) := superpose eq1339 eq1393
  have eq1397 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X2 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1))) := superpose eq1394 eq156
  have eq1399 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X3 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) ◇ ((X4 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X2 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq1394 eq181
  have eq1443 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1))) := superpose eq1333 eq1397
  have eq1445 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X3 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) ◇ ((X4 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq1333 eq1399
  have eq1446 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X3 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq1251 eq1445
  have eq1447 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq945 eq1446
  have eq1448 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq1447 eq728
  have eq1450 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq1447 eq1443
  have eq1455 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq11 eq1450
  have eq1456 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq1455 eq603
  have eq1457 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))))) = X1 := superpose eq1455 eq54
  have eq1516 (X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = X1 := superpose eq1457 eq201
  have eq1517 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ X2) := superpose eq1516 eq15
  have eq1543 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq1517 eq11
  have eq1544 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq1517 eq17
  have eq1550 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (((X3 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X2 ◇ (((X3 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ X0))) := superpose eq1517 eq84
  have eq1675 (X0 X3 X4 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ X0) = (X4 ◇ ((X3 ◇ X0) ◇ (X4 ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X0) ◇ X4)))) := superpose eq1544 eq531
  have eq1683 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) = (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq1544 eq721
  have eq1684 (X0 X3 X4 : G) : (X4 ◇ ((X3 ◇ X0) ◇ (X4 ◇ (X3 ◇ X4)))) = X3 := superpose eq1455 eq1675
  have eq1688 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) = (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq9 eq1683
  have eq1699 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) := superpose eq1688 eq1448
  have eq1700 (X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) = (((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X2 ◇ (((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq1688 eq726
  have eq1701 (X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X1)) = ((X4 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq1550 eq1700
  have eq1702 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := superpose eq1701 eq1456
  have eq1718 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X4 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))))) := superpose eq1701 eq565
  have eq1733 (X1 X3 : G) : (X1 ◇ X1) = ((X3 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq1701 eq1699
  have eq1790 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq1701 eq1702
  have eq1791 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq1701 eq1790
  have eq1792 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq1543 eq1791
  have eq1814 (X0 X4 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X4 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq1701 eq1718
  have eq1831 (X1 X3 : G) : (X1 ◇ X1) = ((X3 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq1455 eq1733
  have eq1832 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq1792 eq1831
  have eq1844 (X0 X4 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X4 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X4 ◇ (X0 ◇ X0)))))) := superpose eq1832 eq1814
  have eq1863 (X0 X4 : G) : (X0 ◇ (X0 ◇ ((X4 ◇ X0) ◇ (X0 ◇ (X4 ◇ X0))))) = X0 := superpose eq1832 eq1844
  have eq1864 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq1684 eq1863
  have eq1870 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq1864 eq1543
  have eq1899 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq1864 eq1870
  have eq1900 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq1864 eq1899
  have eq1901 (X0 X3 : G) : X0 = X3 := superpose eq1900 eq1900
  have eq1903 (X0 : G) : sK0 ≠ X0 := superpose eq1901 eq10
  subsumption eq1903 eq1901


@[equational_result]
theorem Finite.Equation9663_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : ((Y ◇ ((Z ◇ Y) ◇ X)) ◇ ((Y ◇ ((Z ◇ Y) ◇ X)) ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (s ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Z ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Z ◇ Y) ◇ s))) (fun s => (s ◇ (s ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Z Y : G) : ((Z ◇ Y) ◇ ((Y ◇ X) ◇ ((Y ◇ X) ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ Y) ◇ (s ◇ (s ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Z ◇ Y) ◇ (s ◇ (s ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X2 ◇ X0))) = X2 := superpose eq10 eq10
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq12 eq13
  have eq36 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3) := superpose eq10 eq30
  have eq57 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2))) = X1 := superpose eq30 eq13
  have eq68 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X1) = (X3 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)))) := superpose eq30 eq10
  have eq86 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq36 eq15
  have eq185 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ ((X4 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq30 eq57
  have eq221 (X1 X2 X3 : G) : (X2 ◇ X1) = (X3 ◇ X1) := superpose eq185 eq68
  have eq261 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0))) = (((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0)))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0)))))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq86 eq86
  have eq276 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq86 eq12
  have eq277 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))))) = X3 := superpose eq86 eq10
  have eq307 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0)))))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq36 eq261
  have eq312 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq10 eq221
  have eq410 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0))) = ((X3 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq312 eq307
  have eq412 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq312 eq276
  have eq423 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = X3 := superpose eq412 eq277
  have eq431 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0))) = ((X3 ◇ (X3 ◇ X3)) ◇ (X3 ◇ X0)) := superpose eq412 eq410
  have eq468 (X0 X2 X3 : G) : (X3 ◇ (X3 ◇ X0)) = ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X0))) := superpose eq412 eq431
  have eq471 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq468 eq312
  have eq476 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq471 eq423
  have eq491 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) = X0 := superpose eq476 eq12
  have eq538 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq476 eq491
  have eq539 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq476 eq538
  have eq548 (X0 X1 : G) : X0 = X1 := superpose eq539 eq476
  have eq550 (X0 : G) : sK0 ≠ X0 := superpose eq548 eq11
  subsumption eq550 eq548


@[equational_result]
theorem Finite.Equation9667_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq11 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X Y Z : G) : ((Y ◇ ((Z ◇ Y) ◇ X)) ◇ (Y ◇ Y)) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ (Y ◇ Y))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Z ◇ Y) ◇ s))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Z ◇ Y) ◇ s))) (fun s => (s ◇ (Y ◇ Y))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq13 (X Z Y : G) : ((Z ◇ Y) ◇ ((Y ◇ X) ◇ (Y ◇ Y))) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => ((Z ◇ Y) ◇ (s ◇ (Y ◇ Y)))) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ s)) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ s)) (fun s => ((Z ◇ Y) ◇ (s ◇ (Y ◇ Y)))) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq28 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq13 eq13
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq12 eq28
  have eq44 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq34 eq10
  have eq65 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq34 eq44
  have eq66 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq34 eq65
  have eq96 (X0 X2 : G) : X0 = X2 := superpose eq66 eq66
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq11
  subsumption eq98 eq96


@[equational_result]
theorem Finite.Equation9680_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation9680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq12 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X Y Z : G) : ((Y ◇ ((Z ◇ Y) ◇ (Y ◇ X))) ◇ Y) = X := by
    let S : Set G := Set.univ
    have m1 : S.MapsTo (fun s => (s ◇ Y)) S := by
      intro
      simp [S]
    have m2 : S.MapsTo (fun s => (Y ◇ ((Z ◇ Y) ◇ (Y ◇ s)))) S := by
      intro
      simp [S]
    have linv : S.LeftInvOn (fun s => (Y ◇ ((Z ◇ Y) ◇ (Y ◇ s)))) (fun s => (s ◇ Y)) := by
      intro a ha
      simp [S]
      simp [← h]
    have t := linv.surjOn m1
    rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t
    have rinv := Set.InjOn.rightInvOn_of_leftInvOn t.injOn linv m2 m1
    apply rinv _
    simp [S]
  have eq19 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X1) = X3 := superpose eq13 eq13
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq13 eq19
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq13 eq41
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq12
  subsumption eq165 eq89


