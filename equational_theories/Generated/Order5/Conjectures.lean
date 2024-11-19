import equational_theories.FactsSyntax
import equational_theories.EquationalResult
import equational_theories.Equations.All
import Mathlib.Data.Set.Finite.Basic

namespace Conjectures


/--
%---- 18137 => 2
fof(hypothesis, axiom, ![X,Y,Z] : X = mul(mul(Y, X), mul(Z, mul(mul(X, Z), Z))) ).
fof(goal, conjecture, ![X,Y] : X = Y ).
fof(try, axiom, ![X,Y] : ?[XT] : ( X = mul(mul(Y, XT), XT) ) <=> ![XT1,XT2,Y] : ( (mul(mul(Y, XT1), XT1) = mul(mul(Y, XT2), XT2) ) => XT1 = XT2 ) ).

%---- 27863 => 2
fof(hypothesis, axiom, ![X,Y,Z] : X = mul(mul(mul(Y, mul(Y, X)), Y), mul(X, Z)) ).
fof(goal, conjecture, ![X,Y] : X = Y ).
fof(bij, axiom, ![X,Y] : ?[XT] : ( X = mul(XT, mul(XT, Y)) ) <=> ![XT1,XT2,Y] : ( (mul(XT1, mul(XT1, Y)) = mul(XT2, mul(XT2, Y)) ) => XT1 = XT2 ) ).
-/
@[equational_result]
conjecture Finite.Equation18137_implies_Equation2 (G : Type) [Magma G] [Finite G] (_ : Equation18137 G) : Equation2 G
@[equational_result]
conjecture Finite.Equation27863_implies_Equation2 (G : Type) [Magma G] [Finite G] (_ : Equation27863 G) : Equation2 G
