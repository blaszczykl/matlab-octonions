(* ::Package:: *)

(* :Context: Octonions` *)

(* :Title: Octonions *)

(* :Author: Lukasz Blaszczyk *)

(* :Version: Mathematica 11.3 *)

(* :Package Version: 1.0 *)

(* :Keywords:
    octonions, Cayley-Dickson, OFT, octonion Fourier transform
*)

(* :History:
Version 1.0 by Lukasz Blaszczyk, June 2019.
*)

(* :Requirements: *)

(* :Warnings:

    Adds functionality to the following functions:
    Exp, Cos, Sin, Plus, Times, NonCommutativeMultiply,
    Abs, Divide, Re, Sign, Conjugate, Integrate

	More support is given to manipulating objects with the
    Head Octonion than is given to objects of the form
    a + b E1 + c E2 + ... + h E7. In general, the E1, E2, ..., E7 
	form is only usable when doing basic (i.e. addition and multiplication)
    octonion mathematics and using Exp function.

*)

(* :Summary:
This package implements Cayley-Dickson's octonion algebra.
*)

(* :Sources:
*)

BeginPackage["Octonions`", {"Quaternions`"}]

(* Needs[ ]*)

If[Not@ValueQ[AbsE17::usage],AbsE17::usage = "AbsE17[q] gives the absolute value of the pure octonion \
part of q."];

If[Not@ValueQ[SignE17::usage],SignE17::usage = "SignE17[q] gives the sign of the pure octonion \
part of q."];

If[Not@ValueQ[E1::usage],E1::usage = "E1 represents an octonion unit with E1^2 == -1."];

If[Not@ValueQ[E2::usage],E2::usage = "E2 represents an octonion unit with E2^2 == -1."];

If[Not@ValueQ[E3::usage],E3::usage = "E3 represents an octonion unit with E3^2 == -1."];

If[Not@ValueQ[E4::usage],E4::usage = "E4 represents an octonion unit with E4^2 == -1."];

If[Not@ValueQ[E5::usage],E5::usage = "E5 represents an octonion unit with E5^2 == -1."];

If[Not@ValueQ[E6::usage],E6::usage = "E6 represents an octonion unit with E6^2 == -1."];

If[Not@ValueQ[E7::usage],E7::usage = "E7 represents an octonion unit with E7^2 == -1."];

If[Head[L::usage] === MessageName, 
   L::usage = "L represents an octonion unit with L^2 == -1.",
   If[StringPosition[L::usage, "octonion"] === {},
      L::usage = L::usage <> " " <>
      "L also represents an octonion unit with L^2 == -1."
   ]
]

If[Not@ValueQ[NonCommutativeMultiply::usage],NonCommutativeMultiply::usage = "a ** b ** c is a nonassociative \
and non-commutative form of multiplication. It currently implements \
octonion multiplication."];

If[Not@ValueQ[QuadrupleComplexMultiply::usage],QuadrupleComplexMultiply::usage = "QuadrupleComplexMultiply[a, b] is an associative \
and commutative form of multiplication in the algebra of quadruple complex numbers."];

If[Head[Norm::usage] =!= String,
    Norm::usage = "Norm[q] returns Abs[q]^2 when q is an octonion."
]

If[Not@ValueQ[EquivalentO::usage],EquivalentO::usage = "EquivalentO[p,q] gives True if p is equivalent to q, \
i.e. there exists non-zero octonion h such that hp = qh."];

If[Not@ValueQ[Commutator::usage],Commutator::usage = "Commutator[p,q] calculates the commutator [a,b] = ab - ba \
of two octonions a and b."];

If[Not@ValueQ[Associator::usage],Associator::usage = "Associator[p,q,r] calculates the associator [a,b,c] = (ab)c - a(bc) \
of three octonions a, b and c."];

If[Not@ValueQ[Octonion::usage],Octonion::usage = "Octonion[a,b,c,d,e,f,g,h] represents the quaternion \
a + b E1 + c E2 + d E3 + e E4 + f E5 + g E6 + h E7."];

If[Not@ValueQ[IntegerOctonionQ::usage],IntegerOctonionQ::usage = "IntegerOctonionQ[q] gives True if q is an octonion \
with integer coefficients."];

If[Not@ValueQ[OctonionQ::usage],OctonionQ::usage = "OctonionQ[q] gives True if q is an octonion, \
and False otherwise."];

If[Not@ValueQ[ToOctonion::usage],ToOctonion::usage = "ToOctonion[q] transforms q into a Octonion \
object if at all possible."];

If[Not@ValueQ[EToOctonion::usage],EToOctonion::usage = "EToOctonion[n] represents n-th octonion \
imaginary unit."];

If[Not@ValueQ[MultiplicationTableO::usage],MultiplicationTableO::usage = "Multiplication rules in the \
algebra of octonions."];

If[Not@ValueQ[MultiplicationTableF::usage],MultiplicationTableF::usage = "Multiplication rules in the \
algebra of quadruple complex numbers."];

If[Not@ValueQ[FromOctonion::usage],FromOctonion::usage = "FromOctonion[q] transforms the octonion q \
from Octonion[a,b,c,d,e,f,g,h] into the form a + b E1 + c E2 + d E3 + e E4 + f E5 + g E6 + h E7."];

If[Not@ValueQ[OctonionFT::usage],OctonionFT::usage = "OctonionFT[u,x,f] calculates the OFT of \
function u."];


Begin["Private`"]
(* *)
ScalarO[x_]:= (NumericQ[x] && Head[x] =!= Quaternion && Head[x] =!= Complex)

SymbolicO[x_]:= (ScalarO[x] || 
    (Head[x] == Symbol && Not[MemberQ[{E1,E2,E3,E4,E5,E6,E7,J,K,L},x]]))

OctonionQ[a_]:= Head[a] === Octonion && Apply[And,Map[SymbolicO,a]]

MessageOctonionQ[a_, fun_] :=
    If[OctonionQ[a],
        True,
    (* else *)
    Message[Octonion::notoct,1,fun];
    False
    ]

(* Logical operators *)

Octonion /:
	Equal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] :=
	If[x1==y1 && x2==y2 && x3==y3 && x4==y4 && x5==y5 && x6==y6 && x7==y7 && x8==y8,True,False]

Octonion /:
	Equal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Quaternion[y1_,y2_,y3_,y4_]] :=
	If[x1==y1 && x2==y2 && x3==y3 && x4==y4 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Octonion /:
	Equal[Quaternion[y1_,y2_,y3_,y4_], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==y2 && x3==y3 && x4==y4 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Octonion /:
	Equal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Complex[y1_,y2_]] :=
	If[x1==y1 && x2==y2 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Octonion /:
	Equal[Complex[y1_,y2_], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==y2 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Octonion /:
	Equal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], y1_?SymbolicO] :=
	If[x1==y1 && x2==0 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Octonion /:
	Equal[y1_?SymbolicO, Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==0 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Unprotect[Equal]
Do[
Equal[(a_:1)*Evaluate[Symbol["E"<>ToString[n1]]], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	Equal[(a EToOctonion[n1]), (b EToOctonion[n2])]
,{n1,1,7},{n2,1,7}]

Do[
Octonion /:
	Equal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	Equal[Octonion[x1,x2,x3,x4,x5,x6,x7,x8], (b EToOctonion[n2])]
,{n2,1,7}]

Do[
Octonion /:
	Equal[(b_:1)*Evaluate[Symbol["E"<>ToString[n2]]], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	Equal[Octonion[x1,x2,x3,x4,x5,x6,x7,x8], (b EToOctonion[n2])]
,{n2,1,7}]

Do[
Equal[(a_:1), (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	a==b==0
,{n2,1,7}]

Do[
Equal[(b_:1)*Evaluate[Symbol["E"<>ToString[n2]]], (a_:1)] :=
	a==b==0
,{n2,1,7}]
Protect[Equal]

Octonion /:
	Unequal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] :=
	If[x1==y1 && x2==y2 && x3==y3 && x4==y4 && x5==y5 && x6==y6 && x7==y7 && x8==y8,False,True]

Octonion /:
	Unequal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Quaternion[y1_,y2_,y3_,y4_]] :=
	If[x1==y1 && x2==y2 && x3==y3 && x4==y4 && x5==0 && x6==0 && x7==0 && x8==0,False,True]

Octonion /:
	Unequal[Quaternion[y1_,y2_,y3_,y4_], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==y2 && x3==y3 && x4==y4 && x5==0 && x6==0 && x7==0 && x8==0,False,True]

Octonion /:
	Unequal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Complex[y1_,y2_]] :=
	If[x1==y1 && x2==y2 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,False,True]

Octonion /:
	Unequal[Complex[y1_,y2_], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==y2 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,False,True]

Octonion /:
	Unequal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], y1_?SymbolicO] :=
	If[x1==y1 && x2==0 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,False,True]

Octonion /:
	Unequal[y1_?SymbolicO, Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==0 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,False,True]

Unprotect[Unequal]
Do[
Unequal[(a_:1)*Evaluate[Symbol["E"<>ToString[n1]]], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	Unequal[(a EToOctonion[n1]), (b EToOctonion[n2])]
,{n1,1,7},{n2,1,7}]

Do[
Octonion /:
	Unequal[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	Unequal[Octonion[x1,x2,x3,x4,x5,x6,x7,x8], (b EToOctonion[n2])]
,{n2,1,7}]

Do[
Octonion /:
	Unequal[(b_:1)*Evaluate[Symbol["E"<>ToString[n2]]], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	Unequal[Octonion[x1,x2,x3,x4,x5,x6,x7,x8], (b EToOctonion[n2])]
,{n2,1,7}]

Do[
Unequal[(a_:1), (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	Not[a==b==0]
,{n2,1,7}]

Do[
Unequal[(b_:1)*Evaluate[Symbol["E"<>ToString[n2]]], (a_:1)] :=
	Not[a==b==0]
,{n2,1,7}]

Protect[Unequal]

Octonion /:
	EquivalentO[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] :=
	If[x1==y1 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Norm[{y2,y3,y4,y5,y6,y7,y8}],True,False]

Octonion /:
	EquivalentO[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Quaternion[y1_,y2_,y3_,y4_]] :=
	If[x1==y1 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Norm[{y2,y3,y4}],True,False]

Octonion /:
	EquivalentO[Quaternion[y1_,y2_,y3_,y4_], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Norm[{y2,y3,y4}],True,False]

Octonion /:
	EquivalentO[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Complex[y1_,y2_]] :=
	If[x1==y1 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Abs[y2],True,False]

Octonion /:
	EquivalentO[Complex[y1_,y2_], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Abs[y2],True,False]

Octonion /:
	EquivalentO[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], y1_?SymbolicO] :=
	If[x1==y1 && x2==0 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Octonion /:
	EquivalentO[y1_?SymbolicO, Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==y1 && x2==0 && x3==0 && x4==0 && x5==0 && x6==0 && x7==0 && x8==0,True,False]

Do[
EquivalentO[(a_:1)*Evaluate[Symbol["E"<>ToString[n1]]], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] =
	Abs[a]==Abs[b]
,{n1,1,7},{n2,1,7}]

Do[
Octonion /:
	EquivalentO[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	If[x1==0 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Abs[b],True,False]
,{n2,1,7}]

Do[
Octonion /:
	EquivalentO[(b_:1)*Evaluate[Symbol["E"<>ToString[n2]]], Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	If[x1==0 && Norm[{x2,x3,x4,x5,x6,x7,x8}]==Abs[b],True,False]
,{n2,1,7}]

Do[
EquivalentO[(a_:1), (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] :=
	False
,{n2,1,7}]

Do[
EquivalentO[(b_:1)*Evaluate[Symbol["E"<>ToString[n2]]], (a_:1)] :=
	False
,{n2,1,7}]

(* Rules for Plus *)

Octonion /:
	Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_] + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] :=
	Octonion[x1+y1,x2+y2,x3+y3,x4+y4,x5+y5,x6+y6,x7+y7,x8+y8] // OSimplify

Octonion /:
	Quaternion[x1_,x2_,x3_,x4_] + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] :=
	Octonion[x1+y1,x2+y2,x3+y3,x4+y4,y5,y6,y7,y8] // OSimplify

Octonion /:
	Complex[x1_,x2_] + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] :=
	Octonion[x1+y1,x2+y2,y3,y4,y5,y6,y7,y8] // OSimplify

(*Octonion /:
	x1_?ScalarO + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[x1+y1,y2,y3,y4,y5,y6,y7,y8] // OSimplify
*)
Octonion /:
	x1_?SymbolicO + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[x1+y1,y2,y3,y4,y5,y6,y7,y8] // OSimplify

Octonion /:
	x_. E1 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2+x,y3,y4,y5,y6,y7,y8] // OSimplify

Octonion /:
	x_. E2 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3+x,y4,y5,y6,y7,y8] // OSimplify

Octonion /:
	x_. J + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3+x,y4,y5,y6,y7,y8] // OSimplify

Octonion /:
	x_. E3 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4+x,y5,y6,y7,y8] // OSimplify

Octonion /:
	x_. K + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4+x,y5,y6,y7,y8] // OSimplify

Octonion /:
	x_. E4 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4,y5+x,y6,y7,y8] // OSimplify

Octonion /:
	x_. L + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4,y5+x,y6,y7,y8] // OSimplify

Octonion /:
	x_. E5 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4,y5,y6+x,y7,y8] // OSimplify

Octonion /:
	x_. E6 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4,y5,y6,y7+x,y8] // OSimplify

Octonion /:
	x_. E7 + Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Octonion[y1,y2,y3,y4,y5,y6,y7,y8+x] // OSimplify

Unprotect[Plus]
Do[
((a_:1)*Evaluate[Symbol["E"<>ToString[n1]]]) + ((b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]) =
	((a EToOctonion[n1]) + (b EToOctonion[n2]))
,{n1,1,7},{n2,1,7}]
Do[
(a_:1) + ((b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]) =
	((a EToOctonion[0]) + (b EToOctonion[n2]))
,{n2,1,7}]
Protect[Plus]

(* Rules for Times *)
Octonion /:
	a_?SymbolicO * Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]:=
	Octonion[a x1,a x2,a x3,a x4,a x5,a x6,a x7,a x8]

(* Rules for NonCommutativeMultiply *)

Octonion /:
	Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_] ** Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]:=
	Module[
	{q0,q1,q2,q3},
	q0 = Quaternion[x1,x2,x3,x4];
	q1 = Quaternion[x5,x6,x7,x8];
	q2 = Quaternion[y1,y2,y3,y4];
	q3 = Quaternion[y5,y6,y7,y8];
	ToOctonion[Join[
	Apply[List,q0 ** q2 - Conjugate[q3] ** q1],
	Apply[List,q3 ** q0 + q1 ** Conjugate[q2]]
	]]
	] // OSimplify

Unprotect[NonCommutativeMultiply]
SetAttributes[NonCommutativeMultiply,Listable]
ClearAttributes[NonCommutativeMultiply,Flat]

(* Numerous patterns possible when using Complex[] and Quaternion[] numbers *)

EToOctonion[n_] := ToOctonion[Normal[SparseArray[(n+1)-> 1,8]]]

Do[
((a_:1)*Evaluate[Symbol["E"<>ToString[n1]]]) ** ((b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]) =
	a b (EToOctonion[n1] ** EToOctonion[n2])
,{n1,1,7},{n2,1,7}]
a_?SymbolicO ** b_ := a b
a_ ** b_?SymbolicO := a b
(x_ + y_) ** a_:= x**a + y**a
a_ ** (x_ + y_):= a**x + a**y

Quaternion[x1_,x2_,x3_,x4_] ** Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] :=
	Octonion[x1,x2,x3,x4,0,0,0,0] ** Octonion[y1,y2,y3,y4,y5,y6,y7,y8]
Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] ** Quaternion[x1_,x2_,x3_,x4_] :=
	Octonion[y1,y2,y3,y4,y5,y6,y7,y8] ** Octonion[x1,x2,x3,x4,0,0,0,0]
Complex[x1_,x2_] ** Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] :=
	Octonion[x1,x2,0,0,0,0,0,0] ** Octonion[y1,y2,y3,y4,y5,y6,y7,y8]
Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] ** Complex[x1_,x2_] :=
	Octonion[y1,y2,y3,y4,y5,y6,y7,y8] ** Octonion[x1,x2,0,0,0,0,0,0]

Do[
((a_:1)*Evaluate[Symbol["E"<>ToString[n1]]]) ** Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] =
	a EToOctonion[n1] ** Octonion[y1,y2,y3,y4,y5,y6,y7,y8]
,{n1,1,7}]
Do[
Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] ** ((a_:1)*Evaluate[Symbol["E"<>ToString[n1]]]) =
	a Octonion[y1,y2,y3,y4,y5,y6,y7,y8] ** EToOctonion[n1]
,{n1,1,7}]
Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] ** ((a_:1)*b_?SymbolicO) =
	a Octonion[y1,y2,y3,y4,y5,y6,y7,y8] ** b
((a_:1)*b_?SymbolicO) ** Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_] =
	a b ** Octonion[y1,y2,y3,y4,y5,y6,y7,y8]

MultiplicationTableO = Module[
	{table, headings, multtab},
	table = Table[FromOctonion[EToOctonion[i]**EToOctonion[j]],{i,0,7},{j,0,7}];
	headings = Table[FromOctonion[EToOctonion[i]],{i,0,7}];
	multtab = MapThread[Prepend,{ Prepend[table,headings],Prepend[headings,""]}];
	Grid[multtab,Alignment->Center,Spacings->{1.5,1.5},Frame->All,ItemStyle->"Text",Background->{{LightGray,None},{LightGray,None}}]
]

Protect[NonCommutativeMultiply]

(* Multiplication in quadruple complex numbers algebra *)

Octonion /:
	QuadrupleComplexMultiply[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] :=
	Module[
	{s0, s1, s2, s3, t0, t1, t2, t3, V0, V1, V2, V3},
	s0 = x1 + x2 I; s1 = x3 + x4 I; s2 = x5 + x6 I; s3 = x7 + x8 I;
	t0 = y1 + y2 I; t1 = y3 + y4 I; t2 = y5 + y6 I; t3 = y7 + y8 I;
	V0 = s0*t0 - s1*t1 - s2*t2 + s3*t3;
	V1 = s0*t1 + s1*t0 - s2*t3 - s3*t2;
	V2 = s0*t2 + s2*t0 - s1*t3 - s3*t1;
	V3 = s0*t3 + s3*t0 + s1*t2 + s2*t1;
	Octonion[ComplexExpand[Re[V0]],ComplexExpand[Im[V0]],ComplexExpand[Re[V1]],ComplexExpand[Im[V1]],
		ComplexExpand[Re[V2]],ComplexExpand[Im[V2]],ComplexExpand[Re[V3]],ComplexExpand[Im[V3]]]
	]

Do[
QuadrupleComplexMultiply[(a_:1)*Evaluate[Symbol["E"<>ToString[n1]]], (b_:1)*Evaluate[Symbol["E"<>ToString[n2]]]] =
	a b QuadrupleComplexMultiply[EToOctonion[n1], EToOctonion[n2]]
,{n1,1,7},{n2,1,7}]
QuadrupleComplexMultiply[a_?SymbolicO, b_] := a b
QuadrupleComplexMultiply[a_, b_?SymbolicO] := a b
QuadrupleComplexMultiply[x_ + y_, a_] := QuadrupleComplexMultiply[x, a] + QuadrupleComplexMultiply[y, a]
QuadrupleComplexMultiply[a_, x_ + y_] := QuadrupleComplexMultiply[a, x] + QuadrupleComplexMultiply[a, y]

QuadrupleComplexMultiply[Quaternion[x1_,x2_,x3_,x4_], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] :=
	QuadrupleComplexMultiply[Octonion[x1,x2,x3,x4,0,0,0,0], Octonion[y1,y2,y3,y4,y5,y6,y7,y8]]
QuadrupleComplexMultiply[Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_], Quaternion[x1_,x2_,x3_,x4_]] :=
	QuadrupleComplexMultiply[Octonion[y1,y2,y3,y4,y5,y6,y7,y8], Octonion[x1,x2,x3,x4,0,0,0,0]]
QuadrupleComplexMultiply[Complex[x1_,x2_], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] :=
	QuadrupleComplexMultiply[Octonion[x1,x2,0,0,0,0,0,0], Octonion[y1,y2,y3,y4,y5,y6,y7,y8]]
QuadrupleComplexMultiply[Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_], Complex[x1_,x2_]] :=
	QuadrupleComplexMultiply[Octonion[y1,y2,y3,y4,y5,y6,y7,y8], Octonion[x1,x2,0,0,0,0,0,0]]

Do[
QuadrupleComplexMultiply[(a_:1)*Evaluate[Symbol["E"<>ToString[n1]]], Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] =
	a QuadrupleComplexMultiply[EToOctonion[n1], Octonion[y1,y2,y3,y4,y5,y6,y7,y8]]
,{n1,1,7}]
Do[
QuadrupleComplexMultiply[Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_], (a_:1)*Evaluate[Symbol["E"<>ToString[n1]]]] =
	a QuadrupleComplexMultiply[Octonion[y1,y2,y3,y4,y5,y6,y7,y8], EToOctonion[n1]]
,{n1,1,7}]
QuadrupleComplexMultiply[Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_], (a_:1)*b_?SymbolicO] =
	a QuadrupleComplexMultiply[Octonion[y1,y2,y3,y4,y5,y6,y7,y8], b]
QuadrupleComplexMultiply[(a_:1)*b_?SymbolicO, Octonion[y1_,y2_,y3_,y4_,y5_,y6_,y7_,y8_]] =
	a QuadrupleComplexMultiply[b, Octonion[y1,y2,y3,y4,y5,y6,y7,y8]]

MultiplicationTableF = Module[
	{table, headings, multtab},
	table = Table[FromOctonion[QuadrupleComplexMultiply[EToOctonion[i],EToOctonion[j]]],{i,0,7},{j,0,7}];
	headings = Table[FromOctonion[EToOctonion[i]],{i,0,7}];
	multtab = MapThread[Prepend,{ Prepend[table,headings],Prepend[headings,""]}];
	Grid[multtab,Alignment->Center,Spacings->{1.5,1.5},Frame->All,ItemStyle->"Text",Background->{{LightGray,None},{LightGray,None}}]
]

(* Simple functions *)

Octonion /:
	Conjugate[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]] :=
	Octonion[x1,-x2,-x3,-x4,-x5,-x6,-x7,-x8]

Commutator[a_, b_] := (ToOctonion[a] ** ToOctonion[b]) - (ToOctonion[b] ** ToOctonion[a])

Associator[a_, b_, c_] := (ToOctonion[a] ** ToOctonion[b]) ** ToOctonion[c] - ToOctonion[a] ** (ToOctonion[b] ** ToOctonion[c])

Octonion /:
	Norm[a:Octonion[__?SymbolicO]] :=
	Apply[Plus, (Apply[List,a])^2]

Octonion /:
	Abs[a:Octonion[__?SymbolicO]]:=Sqrt[Norm[a]]

Octonion /:
    EvenQ[a:Octonion[__?ScalarO]]:= EvenQ[Norm[a]]

Octonion /:
    OddQ[ a:Octonion[__?ScalarO]]:= OddQ[Norm[a]]

IntegerOctonionQ[a_]:=
    If[OctonionQ[a],
    Mod[2 * List @@ a, 1] == {0,0,0,0,0,0,0,0},
    False
    ]

Octonion /:
	Re[a:Octonion[__?SymbolicO]]:= First[a]

Octonion /:
	Sign[a:Octonion[__?ScalarO]]:= a / Abs[a]

AbsE17[Octonion[x1_?ScalarO,x2_?ScalarO,x3_?ScalarO,x4_?ScalarO,x5_?ScalarO,x6_?ScalarO,x7_?ScalarO,x8_?ScalarO]]:=
	Abs[Octonion[0,x2,x3,x4,x5,x6,x7,x8]]

AbsE17[a_?NumericQ]:=Abs[Im[a]]

SignE17[Octonion[x1_?ScalarO,x2_?ScalarO,x3_?ScalarO,x4_?ScalarO,x5_?ScalarO,x6_?ScalarO,x7_?ScalarO,x8_?ScalarO]]:=
	Sign[Octonion[0,x2,x3,x4,x5,x6,x7,x8]]

Octonion /:
	Im[Octonion[x1_?ScalarO,x2_?ScalarO,x3_?ScalarO,x4_?ScalarO,x5_?ScalarO,x6_?ScalarO,x7_?ScalarO,x8_?ScalarO]]:=
	FromOctonion[Octonion[0,x2,x3,x4,x5,x6,x7,x8]]

(* List of replacement rules that are used to transform exprs into
   Octonion[] objects. *)
tooct = {
	Quaternion[v_,x_,y_,z_]:> Octonion[v,x,y,z,0,0,0,0],
    Complex[x_,y_]:> Octonion[x,y,0,0,0,0,0,0],
    Plus[x_, Times[Complex[0, 1], y_]]:> Octonion[x,y,0,0,0,0,0,0],
    Times[Complex[0, 1], x_]:> Octonion[0,x,0,0,0,0,0,0],
    Times[Complex[0,x_], y_]:> Octonion[0,x y,0,0,0,0,0,0],
    x_. E1:> Octonion[0,x,0,0,0,0,0,0],
	x_. E2:> Octonion[0,0,x,0,0,0,0,0],
    x_.  J:> Octonion[0,0,x,0,0,0,0,0],
    x_. E3:> Octonion[0,0,0,x,0,0,0,0],
	x_.  K:> Octonion[0,0,0,x,0,0,0,0],
	x_. E4:> Octonion[0,0,0,0,x,0,0,0],
	x_.  L:> Octonion[0,0,0,0,x,0,0,0],
	x_. E5:> Octonion[0,0,0,0,0,x,0,0],
	x_. E6:> Octonion[0,0,0,0,0,0,x,0],
	x_. E7:> Octonion[0,0,0,0,0,0,0,x],
	Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_]:> Octonion[x1,x2,x3,x4,x5,x6,x7,x8],
    x_:> Octonion[x,0,0,0,0,0,0,0] /; (SymbolicO[x] || Head[x]=!=List),
	{x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_}:> Octonion[x1,x2,x3,x4,x5,x6,x7,x8]
}

ToOctonion[a_]:= a /. tooct // OSimplify

FromOctonion[a_]:=
    a[[1]] + a[[2]] "E1" + a[[3]] "E2" + a[[4]] "E3" + a[[5]] "E4" + a[[6]] "E5" + a[[7]] "E6" + a[[8]] "E7" /;
    MessageOctonionQ[a, FromOctonion[]]

(* Power of octonions *)

Octonion /:
    Power[a:Octonion[__?ScalarO],0]:= 1

(* Quaternion /:
    Power[a:Octonion[__?ScalarO],n_]:= Power[1/a, -n] /; n < 0 && n != -1
*)
Octonion /:
    Power[a:Octonion[__?ScalarO],-1]:= Conjugate[a] ** 1/Norm[a]

(* Octonion division *)

Octonion /:
    Divide[a:Octonion[__?ScalarO], b:Octonion[__?ScalarO]]:=
    a ** (Conjugate[b] ** 1/Norm[b])

(* Exponential, Trig *)
protected = Unprotect[Exp, Sin, Cos]

Octonion /:
	Exp[a:Octonion[__?ScalarO]]:=
	Exp[Re[a]]*(Cos[AbsE17[a]]+ Sin[AbsE17[a]]*SignE17[a]) // OSimplify

(* Quaternion /:
    Power[E, a:Octonion[__?ScalarO]] := Exp[a]
*)
Do[
Exp[(a_:1)*Evaluate[Symbol["E"<>ToString[n1]]]]=
	ToOctonion[Normal[SparseArray[{1-> Cos[a],(n1+1)-> Sin[a]},8]]] // OSimplify
,{n1,1,7}]

Octonion /:
	Sin[a:Octonion[__?ScalarO]]:=
	-SignE17[a]**(Exp[a ** SignE17[a]] - Exp[-a ** SignE17[a]])/2 // OSimplify

Octonion /:
	Cos[a:Octonion[__?ScalarO]]:=
	-(Exp[a ** SignE17[a]] - Exp[-a ** SignE17[a]])/2 // OSimplify

Protect[ Evaluate[protected] ]
(* Octonion function integration *)

Octonion /:
	Integrate[Octonion[x1_,x2_,x3_,x4_,x5_,x6_,x7_,x8_],{y_,a_,b_}]:=
		ToOctonion[ComplexExpand[Integrate[x1,{y,a,b}]]] +
		ToOctonion[ComplexExpand[Integrate[x2,{y,a,b}]]] ** E1 +
		ToOctonion[ComplexExpand[Integrate[x3,{y,a,b}]]] ** E2 +
		ToOctonion[ComplexExpand[Integrate[x4,{y,a,b}]]] ** E3 +
		ToOctonion[ComplexExpand[Integrate[x5,{y,a,b}]]] ** E4 +
		ToOctonion[ComplexExpand[Integrate[x6,{y,a,b}]]] ** E5 +
		ToOctonion[ComplexExpand[Integrate[x7,{y,a,b}]]] ** E6 +
		ToOctonion[ComplexExpand[Integrate[x8,{y,a,b}]]] ** E7
	
OctonionFT[u_,x_,f_] := Module[
	{U, u1, u2, u3, u4, U1, U2, U3, U4, V1, V2, V3, V4},
    U = ToOctonion[u];
	u1 = FourierTransform[U[[1]]+U[[2]] I, x, f, FourierParameters->{0,-2\[Pi]}];
	u2 = FourierTransform[U[[3]]+U[[4]] I, x, f, FourierParameters->{0,-2\[Pi]}];
	u3 = FourierTransform[U[[5]]+U[[6]] I, x, f, FourierParameters->{0,-2\[Pi]}];
	u4 = FourierTransform[U[[7]]+U[[8]] I, x, f, FourierParameters->{0,-2\[Pi]}];
	U1 = Octonion[ComplexExpand[Re[u1]], ComplexExpand[Im[u1]], 0, 0, 0, 0, 0, 0];
    U2 = Octonion[ComplexExpand[Re[u2]], ComplexExpand[Im[u2]], 0, 0, 0, 0, 0, 0];
    U3 = Octonion[ComplexExpand[Re[u3]], ComplexExpand[Im[u3]], 0, 0, 0, 0, 0, 0];
    U4 = Octonion[ComplexExpand[Re[u4]], ComplexExpand[Im[u4]], 0, 0, 0, 0, 0, 0];
    
	V1 = (U1**(1-E3) + (U1/.{f[[2]]->-f[[2]]})**(1+E3))**(1-E5)
        +((U1/.{f[[3]]->-f[[3]]})**(1-E3) + (U1/.{f[[2]]->-f[[2]],f[[3]]->-f[[3]]})**(1+E3))**(1+E5);
	V2 = ((U2/.{f[[1]]->-f[[1]],f[[3]]->-f[[3]]})**(1-E3) + (U2/.{f[[1]]->-f[[1]],f[[2]]->-f[[2]],f[[3]]->-f[[3]]})**(1+E3))**(1-E5)
        +((U2/.{f[[1]]->-f[[1]]})**(1-E3) + (U2/.{f[[1]]->-f[[1]],f[[2]]->-f[[2]]})**(1+E3))**(1+E5);
	V3 = ((U3/.{f[[1]]->-f[[1]],f[[2]]->-f[[2]]})**(1-E3) + (U3/.{f[[1]]->-f[[1]]})**(1+E3))**(1-E5)
        +((U3/.{f[[1]]->-f[[1]],f[[2]]->-f[[2]],f[[3]]->-f[[3]]})**(1-E3) + (U3/.{f[[1]]->-f[[1]],f[[3]]->-f[[3]]})**(1+E3))**(1+E5);
	V4 = ((U4/.{f[[2]]->-f[[2]],f[[3]]->-f[[3]]})**(1-E3) + (U4/.{f[[3]]->-f[[3]]})**(1+E3))**(1-E5)
        +((U4/.{f[[2]]->-f[[2]]})**(1-E3) + U4**(1+E3))**(1+E5);
    1/4 (V1 + V2 + V3 + V4) // OSimplify
	]


OSimplify[a:Octonion[__?ScalarO]] := Simplify[TrigExpand/@a]
OSimplify[a_] := a

(* *)
Octonion::notoct = "Octonion expected at position `1` in `2`"

End[]  (* Quaternions`Private`*)

EndPackage[] (* Quaternions`*)












