(* This  is all definitions for the Y-part of the model and the two days,  to be imported by coqmodel. *)

Inductive Days := d1 | d2.

(* 
The Y model!
==========================================================================================
 *)

Inductive VY := y0 | y1.
Inductive EdgeY := y0y0 | y0y1 | y1y0 | y1y1| k.

Inductive TriangleY :=
| y0y0_y0y0_y0y0
| y0y1_y0y1_y0y0
| y1y0_y0y0_y0y1
| y1y1_y0y1_y0y1
| k_y0y1_y0y1
| y0y0_y1y0_y1y0
| y0y1_y1y1_y1y0
| y0y1_k_y1y0
| y1y1_y1y1_y1y1
| y1y1_k_y1y1
| k_y1y1_y1y1
| k_k_y1y1
| y1y0_y1y0_k
| y1y1_y1y1_k
| y1y1_k_k
| k_y1y1_k
| k_k_k
| de
| fi.

(* Y simplical functions *)
Function sY (v1 :VY) := match v1 with
                          | y0 => y0y0
                          | y1 => y1y1
                        end.


Function d0Y (e1 :EdgeY) := match e1 with
                              | y0y0 => y0
                              | y0y1 => y1
                              | y1y0 => y0
                              | y1y1 => y1
                              | k => y1
                            end.





Function d1Y (e1 :EdgeY) := match e1 with
                              | y0y0 => y0
                              | y0y1 => y0
                              | y1y0 => y1
                              | y1y1 => y1
                              | k => y1
                            end.



Function se0Y (e1 :EdgeY) :=
  match e1 with
    | k => k_k_y1y1
    | y0y0 => y0y0_y0y0_y0y0
    | y0y1 => y0y1_y0y1_y0y0
    | y1y0 => de
    | y1y1 => y1y1_y1y1_y1y1
  end.

Function se1Y (e1 :EdgeY) :=
  match e1 with
    | k => y1y1_k_k
    | y0y0 => y0y0_y0y0_y0y0
    | y0y1 => y1y1_y0y1_y0y1
    | y1y0 => y0y0_y1y0_y1y0
    | y1y1 => y1y1_y1y1_y1y1
  end.


Function dp0Y (t1 :TriangleY) := 
  match t1 with
    | y0y0_y0y0_y0y0 => y0y0
    | y0y1_y0y1_y0y0 => y0y1
    | y1y0_y0y0_y0y1 => y1y0
    | y1y1_y0y1_y0y1 => y1y1
    | k_y0y1_y0y1 => k
    | y0y0_y1y0_y1y0 => y0y0
    | y0y1_y1y1_y1y0 => y0y1
    | y0y1_k_y1y0 => y0y1
    | de => y1y0
    | y1y1_y1y1_y1y1 => y1y1
    | y1y1_k_y1y1 => y1y1
    | k_y1y1_y1y1 => k
    | k_k_y1y1 => k
    | y1y0_y1y0_k => y1y0
    | y1y1_y1y1_k => y1y1
    | y1y1_k_k => y1y1
    | k_y1y1_k => k
    | k_k_k => k
    | fi => y1y0
  end.





Function dp1Y (t1 :TriangleY) := 
  match t1 with
    | y0y0_y0y0_y0y0 => y0y0
    | y0y1_y0y1_y0y0 => y0y1
    | y1y0_y0y0_y0y1 => y0y0
    | y1y1_y0y1_y0y1 => y0y1
    | k_y0y1_y0y1 => y0y1
    | y0y0_y1y0_y1y0 => y1y0
    | y0y1_y1y1_y1y0 => y1y1
    | y0y1_k_y1y0 => k
    | de => y1y0
    | y1y1_y1y1_y1y1 => y1y1
    | y1y1_k_y1y1 => k
    | k_y1y1_y1y1 => y1y1
    | k_k_y1y1 => k
    | y1y0_y1y0_k => y1y0
    | y1y1_y1y1_k => y1y1
    | y1y1_k_k => k
    | k_y1y1_k => y1y1
    | k_k_k => k
    | fi => y1y0
  end.





Function dp2Y (t1 :TriangleY) := 
  match t1 with
    | y0y0_y0y0_y0y0 => y0y0
    | y0y1_y0y1_y0y0 => y0y0
    | y1y0_y0y0_y0y1 => y0y1
    | y1y1_y0y1_y0y1 => y0y1
    | k_y0y1_y0y1 => y0y1
    | y0y0_y1y0_y1y0 => y1y0
    | y0y1_y1y1_y1y0 => y1y0
    | y0y1_k_y1y0 => y1y0
    | de => y1y1
    | y1y1_y1y1_y1y1 => y1y1
    | y1y1_k_y1y1 => y1y1
    | k_y1y1_y1y1 => y1y1
    | k_k_y1y1 => y1y1
    | y1y0_y1y0_k => k
    | y1y1_y1y1_k => k
    | y1y1_k_k => k
    | k_y1y1_k => k
    | k_k_k => k
    | fi => y1y1
  end.


(* Y equality. It has to come below the simplicial functions since it is defined in day 2 using them*)
Function eqVY (day : Days)(v1 v2 :VY) :=
  match v1, v2 with
    | y0, y0 => true
    | y0, y1 => false
    | y1, y0 => false
    | y1, y1 => true
  end.

Lemma eqEdgeYDec : forall e1 e2 : EdgeY, {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
Defined.


Function sameConstructorEdgeY (e1 e2 :EdgeY) := if (eqEdgeYDec e1 e2) then true else false.

Function eqEdgeY (day : Days)(e1 e2 :EdgeY) :=
  match day with
    | d1 => sameConstructorEdgeY e1 e2
    | d2 =>
      match e1,e2 with
        | y1y1,k | k,y1y1 => true
        | _,_ => sameConstructorEdgeY e1 e2
      end
  end.



Lemma eqtriangleYDec : forall b1 b2 : TriangleY, {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
Defined.

Function sameConstructorTriangleY (t1 t2 :TriangleY) := if (eqtriangleYDec t1 t2) then true else false.

Function eqTriangleY (day : Days)(t1 t2 :TriangleY) :=
  match day with
    | d1 => sameConstructorTriangleY t1 t2
    | d2 =>
      match t1,t2 with
        | de,de => true
        | de,_ | _,de => false
        | _,_ => andb (eqEdgeY d2 (dp0Y t1) (dp0Y t2))  (andb (eqEdgeY d2 (dp1Y t1) (dp1Y t2))   (eqEdgeY d2 (dp2Y t1) (dp2Y t2)))
      end
  end.


(* Y filler functions *)

Function fill12Y (e1 e2 :EdgeY) := 
  match e1,e2 with  
    |   y0y0,  y1y0=> y0y0_y1y0_y1y0
    |   y1y1,  y0y1=> y1y1_y0y1_y0y1
    |   y0y1,  k=> y0y1_k_y1y0
    |   k,  k=> k_k_y1y1
    |   y1y0,  y1y0=> fi
    |   y0y0,  y0y0=> y0y0_y0y0_y0y0
    |   k,  y1y1=> k_y1y1_y1y1
    |   y1y0,  y0y0=> y1y0_y0y0_y0y1
    |   y0y1,  y0y1=> y0y1_y0y1_y0y0
    |   k,  y0y1=> k_y0y1_y0y1
    |   y0y1,  y1y1=> y0y1_y1y1_y1y0
    |   y1y1,  k=> y1y1_k_y1y1
    |   y1y1,  y1y1=> y1y1_y1y1_y1y1
    | _ ,_ => y0y0_y0y0_y0y0
  end.

Function fill11Y (e1 e2 :EdgeY) := 
  match e1,e2 with  
    |   y0y0,  y1y0=> y0y0_y1y0_y1y0
    |   y1y1,  y0y1=> y1y1_y0y1_y0y1
    |   k,  k=> k_y1y1_k
    |   y0y1,  y0y0=> y0y1_y0y1_y0y0
    |   y1y0,  y0y1=> y1y0_y0y0_y0y1
    |   y1y0,  y1y1=> fi
    |   y0y0,  y0y0=> y0y0_y0y0_y0y0
    |   y1y0,  k=> y1y0_y1y0_k
    |   k,  y1y1=> k_y1y1_y1y1
    |   k,  y0y1=> k_y0y1_y0y1
    |   y1y1,  k=> y1y1_y1y1_k
    |   y1y1,  y1y1=> y1y1_y1y1_y1y1
    |   y0y1,  y1y0=> y0y1_y1y1_y1y0
    | _ ,_ => y0y0_y0y0_y0y0
  end.

Function fill10Y (e1 e2 :EdgeY) := 
  match e1,e2 with  
    |   k,  k=> y1y1_k_k
    |   y0y1,  y0y0=> y0y1_y0y1_y0y0
    |   y0y0,  y0y1=> y1y0_y0y0_y0y1
    |   k,  y1y0=> y0y1_k_y1y0
    |   y1y0,  y1y0=> y0y0_y1y0_y1y0
    |   y1y0,  y1y1=> fi
    |   y0y0,  y0y0=> y0y0_y0y0_y0y0
    |   y1y0,  k=> y1y0_y1y0_k
    |   k,  y1y1=> y1y1_k_y1y1
    |   y0y1,  y0y1=> y1y1_y0y1_y0y1
    |   y1y1,  k=> y1y1_y1y1_k
    |   y1y1,  y1y1=> y1y1_y1y1_y1y1
    |   y1y1,  y1y0=> y0y1_y1y1_y1y0
    | _ ,_ => y0y0_y0y0_y0y0
  end.



(* Maps triangle-compatible edges a b c to a triangle t which have d0 t = a, d1 t = b and
d2t = c. For the choice between de and fi it maps to fi. It maps every tupple of
non-compatible edges to y0y0_y0y0_y0y0 for no particular reason. *)

Function edgesToTriangle(d0 d1 d2 :EdgeY) :=
  match d0,d1,d2 with
    | y0y0, y0y0, y0y0 => y0y0_y0y0_y0y0
    | y0y1, y0y1, y0y0 => y0y1_y0y1_y0y0
    | y1y0, y0y0, y0y1 => y1y0_y0y0_y0y1
    | y1y1, y0y1, y0y1 => y1y1_y0y1_y0y1
    | k, y0y1, y0y1 => k_y0y1_y0y1
    | y0y0, y1y0, y1y0 => y0y0_y1y0_y1y0
    | y0y1, y1y1, y1y0 => y0y1_y1y1_y1y0
    | y0y1, k, y1y0 => y0y1_k_y1y0
    | y1y1, y1y1, y1y1 => y1y1_y1y1_y1y1
    | y1y1, k, y1y1 => y1y1_k_y1y1
    | k, y1y1, y1y1 => k_y1y1_y1y1
    | k, k, y1y1 => k_k_y1y1
    | y1y0, y1y0, k => y1y0_y1y0_k
    | y1y1, y1y1, k => y1y1_y1y1_k
    | y1y1, k, k => y1y1_k_k
    | k, y1y1, k => k_y1y1_k
    | k, k, k => k_k_k
    | y1y0, y1y0, y1y1 => fi
    |  _,  _,_ => y0y0_y0y0_y0y0
  end.


Function fill20Y (t1 t2 t3 :TriangleY) := (edgesToTriangle (dp0Y t1) (dp0Y t2) (dp0Y t3)).
Function fill21Y (t1 t2 t3 :TriangleY) := (edgesToTriangle (dp0Y t1) (dp1Y t2) (dp1Y t3)).
Function fill22Y (t1 t2 t3 :TriangleY) := (edgesToTriangle (dp1Y t1) (dp1Y t2) (dp2Y t3)).
Function fill23Y (t1 t2 t3 :TriangleY) := (edgesToTriangle (dp2Y t1) (dp2Y t2) (dp2Y t3)).


(* End Y model *)