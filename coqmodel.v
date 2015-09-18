(* This file contain the X-part and Delta-part, in addition to all the theorems. It imports the Y-part,
located in ymodel.  Verifying this file can take a few minutes on a modern machine *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Load ymodel.


Section KripkeModel.
 
  Inductive VX:= x.
  Inductive EdgeX:= sx | e.
  Inductive TriangleX:=
  | sx_sx_sx
  | sx_e_sx 
  | e_sx_sx 
  | e_e_sx 
  | sx_sx_e
  | sx_e_e 
  | e_sx_e 
  | e_e_e.
  
  
  Function sX (v1:VX):= sx.

  Function d0X (e1:EdgeX):= x.
  Function d1X (e1:EdgeX):= x.

  Function se0X (e1:EdgeX):=
    match e1 with
      | sx => sx_sx_sx
      | e => e_e_sx
    end.
  
  Function se1X (e1:EdgeX):=
    match e1 with
      | sx => sx_sx_sx
      | e => sx_e_e
    end.



  
  Function dp0X (t1:TriangleX):= 
    match t1 with
      | sx_sx_sx => sx
      | sx_e_sx => sx
      | e_sx_sx => e
      | e_e_sx => e
      | sx_sx_e => sx
      | sx_e_e => sx
      | e_sx_e => e
      | e_e_e => e
    end.




  Function dp1X (t1:TriangleX):= 
    match t1 with
      | sx_sx_sx => sx
      | sx_e_sx => e
      | e_sx_sx => sx
      | e_e_sx => e
      | sx_sx_e => sx
      | sx_e_e => e
      | e_sx_e => sx
      | e_e_e => e
    end.




  Function dp2X (t1:TriangleX):= 
    match t1 with
      | sx_sx_sx => sx
      | sx_e_sx => sx
      | e_sx_sx => sx
      | e_e_sx => sx
      | sx_sx_e => e
      | sx_e_e => e
      | e_sx_e => e
      | e_e_e => e
    end.


  Function eqVX (day: Days)(v1 v2:VX):= true.
  
  Lemma eqEdgeXDec: forall e1 e2: EdgeX, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
  Defined.
  
  Function sameConstructorEdgeX (e1 e2:EdgeX):= if (eqEdgeXDec e1 e2) then true else false.

  Function eqEdgeX (day: Days)(e1 e2:EdgeX):=
    match day with
      | d1 => sameConstructorEdgeX e1 e2
      | d2 => true
    end.
  

  Lemma eqtriangleXDec: forall b1 b2: TriangleX, {b1 = b2} + {b1 <> b2}.
  Proof.
    decide equality.
  Defined.
  
  Function sameConstructorTriangleX (t1 t2:TriangleX):= if (eqtriangleXDec t1 t2) then true else false.
  
  Function eqTriangleX (day: Days)(t1 t2:TriangleX):=
    match day with
      | d1 => sameConstructorTriangleX t1 t2
      | d2 => true
    end.


  Function edgesToTriangleX(d0 d1 d2 :EdgeX) :=
    match d0,d1,d2 with
      | sx, sx, sx => sx_sx_sx
      | sx, e, sx => sx_e_sx
      | e, sx, sx => e_sx_sx
      | e, e, sx => e_e_sx
      | sx, sx, e => sx_sx_e
      | sx, e, e => sx_e_e
      | e, sx, e => e_sx_e
      | e, e, e => e_e_e
    end.


  Function fill20X (t1 t2 t3 :TriangleX) :=  (edgesToTriangleX (dp0X t1) (dp0X t2) (dp0X t3)).

  Function fill21X (t1 t2 t3 :TriangleX) :=  (edgesToTriangleX (dp0X t1) (dp1X t2) (dp1X t3)).

  Function fill22X (t1 t2 t3 :TriangleX) := (edgesToTriangleX (dp1X t1) (dp1X t2) (dp2X t3)).

  Function fill23X (t1 t2 t3 :TriangleX) := (edgesToTriangleX (dp2X t1) (dp2X t2) (dp2X t3)).
 
  
  Function fill12X (t1 t2  :EdgeX) := 
    match t1,t2 with  
      |   sx,  e=> sx_e_sx
      |   e,  e=> e_e_sx
      |   sx,  sx=> sx_sx_sx
      |   e,  sx=> e_sx_sx
    end.   


  Function fill11X (t1 t2  :EdgeX) := 
    match t1,t2 with  
      |   sx,  e=> sx_sx_e
      |   e,  e=> e_sx_e
      |   sx,  sx=> sx_sx_sx
      |   e,  sx=> e_sx_sx
    end.               

  Function fill10X (t1 t2  :EdgeX) := 
    match t1,t2 with  
      |   sx,  e=> sx_sx_e
      |   e,  e=> sx_e_e
      |   sx,  sx=> sx_sx_sx
      |   e,  sx=> sx_e_sx
    end.
  
  


  Inductive Delta10:= delta0 | delta1 .
  Inductive Delta11:= delta00 | delta01 | delta11.
  Inductive Delta12:=
  | delta000
  | delta001
  | delta011
  | delta111.

  Function s (v:Delta10):= match v with
                             | delta0 => delta00
                             | delta1 => delta11
                           end.

  Function s0 (e:Delta11):= match e with
                              | delta00 => delta000
                              | delta01 => delta001
                              | delta11 => delta111
                            end.

  Function s1 (e:Delta11):= match e with
                              | delta00 => delta000
                              | delta01 => delta011
                              | delta11 => delta111
                            end.
  
  Function dv0 (e:Delta11):= match e with
                               | delta00 => delta0
                               | delta01 => delta1
                               | delta11 => delta1
                             end.

  Function dv1 (e:Delta11):= match e with
                               | delta00 => delta0
                               | delta01 => delta0
                               | delta11 => delta1
                             end.

  
  Function dp0 (t:Delta12):= match t with
                               | delta000 => delta00
                               | delta001 => delta01
                               | delta011 => delta11
                               | delta111 => delta11
                             end.

  Function dp1 (t:Delta12):= match t with
                               | delta000 => delta00
                               | delta001 => delta01
                               | delta011 => delta01
                               | delta111 => delta11
                             end.
  
  Function dp2 (t:Delta12):= match t with
                               | delta000 => delta00
                               | delta001 => delta00
                               | delta011 => delta01
                               | delta111 => delta11
                             end.

  Lemma eqDelta10Dec: forall e1 e2: Delta10, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
  Defined.
  
  Function eqDelta10 (day: Days)(e1 e2:Delta10):= if (eqDelta10Dec e1 e2) then true else false.

  Lemma eqDelta11Dec: forall e1 e2: Delta11, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
  Defined.
  
  Function eqDelta11 (day: Days)(e1 e2:Delta11):= if (eqDelta11Dec e1 e2) then true else false.

  Lemma eqDelta12Dec: forall e1 e2: Delta12, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
  Defined.
  
  Function eqDelta12 (day: Days)(e1 e2:Delta12):= if (eqDelta12Dec e1 e2) then true else false.


  
  
  Function Fv (delt:Delta10) (v:VX):=
    match delt with
      | delta0 => y0
      | delta1 => y1
    end.
  
  
  Function Fe (delt:Delta11) (e:EdgeX):=
    match delt with
      | delta00 => y0y0
      | delta01 => y0y1
      | delta11 => match e with
                     | sx => y1y1
                     | e => k
                   end
    end.                      

  
  Function Ft000 (t:TriangleX):= y0y0_y0y0_y0y0.
  Function Ft001 (t:TriangleX):= y0y1_y0y1_y0y0.

  Function Ft011 (t:TriangleX):=
    match t with
      | sx_sx_sx => y1y1_y0y1_y0y1
      | sx_e_sx => y1y1_y0y1_y0y1
      | e_sx_sx => k_y0y1_y0y1
      | e_e_sx => k_y0y1_y0y1
      | sx_sx_e => y1y1_y0y1_y0y1
      | sx_e_e => y1y1_y0y1_y0y1
      | e_sx_e => k_y0y1_y0y1
      | e_e_e => k_y0y1_y0y1
    end.         
  
  Function Ft111 (t:TriangleX):=
    match t with
      | sx_sx_sx => y1y1_y1y1_y1y1
      | sx_e_sx => y1y1_k_y1y1
      | e_sx_sx => k_y1y1_y1y1
      | e_e_sx => k_k_y1y1
      | sx_sx_e => y1y1_y1y1_k
      | sx_e_e => y1y1_k_k
      | e_sx_e => k_y1y1_k
      | e_e_e => k_k_k
    end.         

  Function Ft (delt:Delta12) (t:TriangleX):=
    match delt with
      | delta000 => Ft000 t
      | delta001 => Ft001 t
      | delta011 => Ft011 t
      | delta111 => Ft111 t
    end. 


  Definition ReflexiveFun {A:Type}(eqFun: Days -> A -> A -> bool):= forall (d:Days)(el:A), (eqFun d el el) = true.
  Hint Unfold ReflexiveFun.

  Definition SymetricFun {A:Type}(eqFun: Days -> A -> A -> bool):= 
    forall (d:Days)(elem1 elem2:A),  ((eqFun d elem1 elem2)=true)->(eqFun d elem2 elem1)=true.
  Hint Unfold SymetricFun.
  
  Definition TransitiveFun {A:Type}(eqFun: Days -> A -> A -> bool):=
    forall (d:Days)(elem1 elem2 elem3:A),
      ((eqFun d elem1 elem2)=true /\ (eqFun d elem2 elem3)=true) ->
      (eqFun d elem1 elem3)=true.
  Hint Unfold TransitiveFun.
  
  Definition EquivalenceFun {A:Type}(eqFun: Days -> A -> A -> bool):=
    ReflexiveFun eqFun /\ SymetricFun eqFun /\ TransitiveFun eqFun.
  Hint Unfold EquivalenceFun.
  

  Definition unaryFunctionRespectsEquality {Domain CoDomain:Type}
             (eqDomain: Days -> Domain -> Domain -> bool)
             (eqCoDomain: Days -> CoDomain -> CoDomain -> bool)
             (function: Domain->CoDomain):=
    forall d:Days, forall (elem1 elem2: Domain),
      (eqDomain d elem1 elem2)=true -> (eqCoDomain d (function elem1) (function elem2))=true.

  Definition binaryFunctionRespectsEquality {Domain CoDomain:Type}
             (eqDomain: Days -> Domain -> Domain -> bool)
             (eqCoDomain: Days -> CoDomain -> CoDomain -> bool)
             (function: Domain-> Domain -> CoDomain):=
    forall d:Days, forall (elem1 elem1p elem2 elem2p: Domain),
      (eqDomain d elem1 elem1p)=true /\ (eqDomain d elem2 elem2p)=true
      -> (eqCoDomain d (function elem1 elem2) (function elem1p elem2p))=true.


  Definition tertaryFunctionRespectsEquality {Domain CoDomain:Type}
             (eqDomain: Days -> Domain -> Domain -> bool)
             (eqCoDomain: Days -> CoDomain -> CoDomain -> bool)
             (function: Domain-> Domain-> Domain -> CoDomain):=
    forall d:Days, forall (elem1 elem2 elem3 elem1p elem2p elem3p: Domain),
      ((eqDomain d elem1 elem1p)=true /\
       (eqDomain d elem2 elem2p)=true /\
       (eqDomain d elem3 elem3p)=true)
      -> (eqCoDomain d (function elem1 elem2 elem3)
                       (function elem1p elem2p elem3p))=true.

  Hint Unfold unaryFunctionRespectsEquality.
  Hint Unfold binaryFunctionRespectsEquality.
  Hint Unfold tertaryFunctionRespectsEquality.

  (* A tertary function which respects equality on each of its 3 arguments respect it on all. *)
  Theorem TertaryFunctionRespectsEqualtyPointwise (Domain CoDomain :Type)
          (function : Domain -> Domain -> Domain -> CoDomain)
          (eqDomain : Days-> Domain -> Domain -> bool)
          (eqCoDomain :Days->  CoDomain -> CoDomain -> bool)
          (eqCoDomainIsEqiv : EquivalenceFun eqCoDomain)
  :
    (forall (d:Days)(t1 t2 t3:Domain) (t1p:Domain),
       (eqDomain d t1 t1p)=true -> (eqCoDomain d (function t1 t2 t3) (function t1p t2 t3))=true)
    ->
    (forall (d:Days)(t1 t2 t3:Domain) (t2p:Domain),
       (eqDomain d t2 t2p)=true -> (eqCoDomain d (function t1 t2 t3) (function t1 t2p t3))=true)
    ->
    (forall (d:Days)(t1 t2 t3:Domain) (t3p:Domain),
       (eqDomain d t3 t3p)=true -> (eqCoDomain d (function t1 t2 t3) (function t1 t2 t3p))=true)
    -> tertaryFunctionRespectsEquality eqDomain eqCoDomain function.
  Proof.
    unfold tertaryFunctionRespectsEquality.
    intros.
    destruct  H2.
    destruct H3.
    set(eqCoDomainTrans:= (proj2 (proj2 eqCoDomainIsEqiv ))).
    assert (eqCoDomain d (function elem1 elem2 elem3) (function elem1p elem2 elem3)=true);auto.
    assert (eqCoDomain d (function elem1p elem2 elem3) (function elem1p elem2p elem3)=true);auto.
    assert (eqCoDomain d (function elem1p elem2p elem3) (function elem1p elem2p elem3p)=true);auto.
    assert (eqCoDomain d (function elem1 elem2 elem3) (function elem1p elem2p elem3)=true);auto.
    assert ( eqCoDomain d (function elem1 elem2 elem3) (function elem1p elem2 elem3) = true
             /\ eqCoDomain d (function elem1p elem2 elem3) (function elem1p elem2p elem3) = true);auto.
    unfold EquivalenceFun in eqCoDomainIsEqiv.
    
    apply (eqCoDomainTrans d (function elem1 elem2 elem3) (function elem1p elem2 elem3) (function elem1p elem2p elem3));auto.
    apply (eqCoDomainTrans d (function elem1 elem2 elem3) (function elem1p elem2p elem3) (function elem1p elem2p elem3p));auto.
  Qed.

  
  Definition EqFunctionMonotone {Domain:Type}
             (eq: Days -> Domain -> Domain -> bool):=
             forall (elem1 elem2: Domain),
               (eq d1 elem1 elem2)=true -> (eq d2 elem1 elem2)=true.

  Hint Unfold EqFunctionMonotone.
  
  (* Note that for every equivalence function Eq we have that a=b implies
  Eq a b = true. So if we want to proove A -> Eq a b = true we can instead prove A -> a=b. We sometimes do this for effeciency reasons.
   *)
  Class twoDayKripke (Points Edges Triangles :Type)
    :=  {
        sP : Points -> Edges;
        d0E : Edges -> Points;
        d1E : Edges -> Points;
        s0E : Edges -> Triangles;
        s1E : Edges -> Triangles;
        d0T : Triangles -> Edges;
        d1T : Triangles -> Edges;
        d2T : Triangles -> Edges;
        eqV : Days -> Points -> Points -> bool;
        eqEdges : Days -> Edges -> Edges -> bool;
        eqTriangles : Days -> Triangles -> Triangles -> bool;
        eqVisEq : EquivalenceFun eqV;
        eqEdgessisEq : EquivalenceFun eqEdges;
        eqTrianglesisEq : EquivalenceFun eqTriangles;
        _ : EqFunctionMonotone eqV;
        _ : EqFunctionMonotone eqEdges;
        _ : EqFunctionMonotone eqTriangles;
        sPRespectsEq : unaryFunctionRespectsEquality eqV eqEdges sP;
        d0ERespectsEq : unaryFunctionRespectsEquality eqEdges eqV  d0E;
        d1ERespectsEq : unaryFunctionRespectsEquality eqEdges eqV  d1E;
        s0ERespectsEq : unaryFunctionRespectsEquality eqEdges eqTriangles  s0E;
        s1ERespectsEq : unaryFunctionRespectsEquality eqEdges eqTriangles  s1E;
        d0TRespectsEq : unaryFunctionRespectsEquality  eqTriangles eqEdges  d0T;
        d1TRespectsEq : unaryFunctionRespectsEquality  eqTriangles eqEdges  d1T;
        d2TRespectsEq : unaryFunctionRespectsEquality  eqTriangles eqEdges  d2T;
        (* Simplicial identity 1 *)
        _: forall t: Triangles, d0E(d1T(t)) = d0E(d0T(t));
        _: forall t: Triangles, d0E(d2T(t)) = d1E(d0T(t));
        _: forall t: Triangles, d1E(d2T(t)) = d1E(d1T(t));
        (* Simplicial identity 2 *)
        _: forall e: Edges, d0T(s1E(e)) = sP(d0E(e)) ;
        (* Simplicial identity 3 *)
        _: forall p: Points, d0E(sP(p)) = p; 
        _: forall p: Points, d1E(sP(p)) = p; 
        _: forall e: Edges,  d0T(s0E(e)) = e; 
        _: forall e: Edges,  d1T(s0E(e)) = e; 
        _: forall e: Edges,  d1T(s1E(e)) = e; 
        _: forall e: Edges,  d2T(s1E(e)) = e; 
        (* Simplicial identity 4  *)
        _ : forall e:Edges, d2T(s0E(e)) = sP(d1E(e));
        (* Simplicial identity 5 *)
        _: forall p: Points, s1E(sP(p)) = s0E(sP(p))
      }.

  Class fillableModel {Points Edges Triangles:Type} {m: twoDayKripke Points Edges Triangles}
    :=  {
        fill10: Edges -> Edges -> Triangles;
        fill11: Edges -> Edges -> Triangles;
        fill12: Edges -> Edges -> Triangles;
        fill20: Triangles -> Triangles -> Triangles -> Triangles;
        fill21: Triangles -> Triangles -> Triangles -> Triangles;
        fill22: Triangles -> Triangles -> Triangles -> Triangles;
        fill23: Triangles -> Triangles -> Triangles -> Triangles;

        fill10RespectEquality:  binaryFunctionRespectsEquality eqEdges eqTriangles fill10;
        fill11RespectEquality:  binaryFunctionRespectsEquality eqEdges eqTriangles fill11;
        fill12RespectEquality:  binaryFunctionRespectsEquality eqEdges eqTriangles fill12;       
        fill20RespectsEqualty:  tertaryFunctionRespectsEquality eqTriangles eqTriangles fill20;
        fill21RespectsEqualty:  tertaryFunctionRespectsEquality eqTriangles eqTriangles fill21;
        fill22RespectsEqualty:  tertaryFunctionRespectsEquality eqTriangles eqTriangles fill22;
        fill23RespectsEqualty:  tertaryFunctionRespectsEquality eqTriangles eqTriangles fill23;
        
        fill10Prop: forall (d:Days)(e1 e2:Edges),  ((eqV d (d1E e1) (d1E e2))=true)->
                                                   (eqEdges d (d1T (fill10 e1 e2)) e1)=true /\
                                                   (eqEdges d (d2T (fill10 e1 e2)) e2)=true;
        
        fill11Prop: forall (d:Days)(e1 e2:Edges),  ((eqV d (d1E e1) (d0E e2))=true)->
                                                   (eqEdges d (d0T (fill11 e1 e2)) e1)=true /\
                                                   (eqEdges d (d2T (fill11 e1 e2)) e2)=true;
        
        fill12Prop: forall (d:Days)(e0 e1:Edges),  ((eqV d (d0E e0) (d0E e1))=true)->
                                                   (eqEdges d (d0T (fill12 e0 e1)) e0)=true /\
                                                   (eqEdges d (d1T (fill12 e0 e1)) e1)=true;

        fill20Prop: forall (d:Days)(t1 t2 t3:Triangles),  (eqEdges d (d1T t1) (d1T t2))=true /\
                                                          (eqEdges d (d2T t1) (d1T t3))=true /\
                                                          (eqEdges d (d2T t2) (d2T t3))=true ->
                                                          (
                                                            (eqEdges d (d0T t1) (d0T (fill20 t1 t2 t3)))=true /\
                                                            (eqEdges d (d0T t2) (d1T (fill20 t1 t2 t3)))=true   /\
                                                            (eqEdges d (d0T t3) (d2T (fill20 t1 t2 t3)))=true);
        fill21Prop: forall (d:Days)(t1 t2 t3:Triangles),
                      (eqEdges d (d1T t1) (d0T t2))=true /\
                      (eqEdges d (d2T t1) (d0T t3))=true /\
                      (eqEdges d (d2T t2) (d2T t3))=true ->
                      ((eqEdges d (d0T t1) (d0T (fill21 t1 t2 t3)))=true /\
                       (eqEdges d (d1T t2) (d1T (fill21 t1 t2 t3)))=true  /\
                       (eqEdges d (d1T t3) (d2T (fill21 t1 t2 t3)))=true);

        fill22Prop: forall (d:Days)(t1 t2 t3:Triangles),
                      (eqEdges d (d0T t1) (d0T t2))=true /\
                      (eqEdges d (d2T t1) (d0T t3))=true /\
                      (eqEdges d (d2T t2) (d1T t3))=true ->
                      ((eqEdges d (d1T t1) (d0T (fill22 t1 t2 t3)))=true /\
                       (eqEdges d (d1T t2) (d1T (fill22 t1 t2 t3)))=true  /\
                       (eqEdges d (d2T t3) (d2T (fill22 t1 t2 t3)))=true);

        fill23Prop: forall (d:Days)(t1 t2 t3:Triangles),
                      (eqEdges d (d0T t1) (d0T t2))=true /\
                      (eqEdges d (d1T t1) (d0T t3))=true /\
                      (eqEdges d (d1T t2) (d1T t3))=true ->
                      ((eqEdges d (d2T t1) (d0T (fill23 t1 t2 t3)))=true /\
                       (eqEdges d (d2T t2) (d1T (fill23 t1 t2 t3)))=true  /\
                       (eqEdges d (d2T t3) (d2T (fill23 t1 t2 t3)))=true)       
                        
      }.

  
  Ltac destructGroundElement Points Edges Triangles:=
    repeat   (match goal with
                | [elem : Points |- _] =>  destruct elem
                | [elem : Edges |- _] =>  destruct elem
                | [elem : Triangles |- _] =>  destruct elem
                | [elem : Days |- _] =>  destruct elem
                | [_:_ |- _] =>  auto
              end).
  

  Program  Instance DeltaModel : twoDayKripke Delta10 Delta11 Delta12 := {|
                                                                          sP:= s;
                                                                          eqV := eqDelta10;
                                                                          eqEdges := eqDelta11;
                                                                          eqTriangles := eqDelta12;
                                                                          d0E := dv0;
                                                                          d1E := dv1;
                                                                          s0E := s0;
                                                                          s1E := s1;
                                                                          d0T := dp0;
                                                                          d1T := dp1;
                                                                          d2T :=dp2
                                                                        |}.
  Solve All Obligations using (autounfold; repeat split;autounfold;intros;(destructGroundElement Delta10 Delta11 Delta12);trivial;destruct H;trivial).
  
  
  Program  Instance XModel : twoDayKripke VX EdgeX TriangleX := {|
                                                                 sP:= sX;
                                                                 eqV := eqVX;
                                                                 eqEdges := eqEdgeX;
                                                                 eqTriangles := eqTriangleX;
                                                                 d0E := d0X;
                                                                 d1E := d1X;
                                                                 s0E := se0X;
                                                                 s1E := se1X;
                                                                 d0T := dp0X;
                                                                 d1T := dp1X;
                                                                 d2T :=dp2X
                                                               |}.
  Solve All Obligations using (  autounfold; repeat split;autounfold;intros;(destructGroundElement VX EdgeX TriangleX);trivial;destruct H;trivial).



  

  
  Program  Instance XModelFill :  fillableModel  := {|
                                                     fill10:=fill10X;
                                                     fill11:=fill11X;
                                                     fill12:=fill12X;
                                                     fill20:=fill20X;
                                                     fill21:=fill21X;
                                                     fill22:=fill22X;
                                                     fill23:=fill23X
                                                   |}.
  Obligation 4.
  apply TertaryFunctionRespectsEqualtyPointwise; try (apply XModel_obligation_3);
  intros;(destructGroundElement VX EdgeX TriangleX);trivial.
  Qed.
  Obligation 5.
  apply TertaryFunctionRespectsEqualtyPointwise; try (apply XModel_obligation_3);
  intros;(destructGroundElement VX EdgeX TriangleX);trivial.
  Qed.
  Obligation 6.
  apply TertaryFunctionRespectsEqualtyPointwise; try (apply XModel_obligation_3);
  intros;(destructGroundElement VX EdgeX TriangleX);trivial.
  Qed.
  Obligation 7.
  apply TertaryFunctionRespectsEqualtyPointwise; try (apply XModel_obligation_3);
  intros;(destructGroundElement VX EdgeX TriangleX);trivial.
  Qed.
  Solve All Obligations using (  autounfold; repeat split;autounfold;intros;(destructGroundElement VX EdgeX TriangleX);trivial;destruct H;destruct H0;trivial).

  
  Program  Instance YModel : twoDayKripke VY EdgeY TriangleY := {|
                                                                 sP:= sY;
                                                                 eqV := eqVY;
                                                                 eqEdges := eqEdgeY;
                                                                 eqTriangles := eqTriangleY;
                                                                 d0E := d0Y;
                                                                 d1E := d1Y;
                                                                 s0E := se0Y;
                                                                 s1E := se1Y;
                                                                 d0T := dp0Y;
                                                                 d1T := dp1Y;
                                                                 d2T :=dp2Y
                                                               |}.
  Obligation 3.
  autounfold; repeat split;autounfold;intros.
  destruct d;destruct el;auto.
  destruct d;destruct elem1;destruct elem2;trivial.
  destruct d;destruct elem1;destruct elem2;trivial;destruct H;destruct elem3;trivial.
  Qed.
  Solve All Obligations using (  autounfold; repeat split;autounfold;intros;(destructGroundElement VY EdgeY TriangleY);trivial;destruct H;trivial).




  Theorem eqVertexYday1Minimal: forall (p1 p2:VY),  (eqVY d1 p1 p2)=true -> p1=p2.
  Proof.
    intros.
    simpl in H.
    destruct p1; destruct p2;auto; simpl in H; contradict H;  apply diff_false_true.
  Qed.
  Theorem eqEdgeYday1Minimal: forall (e1 e2:EdgeY),  (eqEdgeY d1 e1 e2)=true -> e1=e2.
  Proof.  
    intros.
    simpl in H.
    unfold sameConstructorEdgeY in H.
    destruct (eqEdgeYDec e1 e2);trivial.
    contradict H.
    apply diff_false_true.
  Qed. 
  
  
  Theorem eqTriangleYday1Minimal: forall (t1 t2:TriangleY),  (eqTriangleY d1 t1 t2)=true -> t1=t2.
  Proof.  
    intros.
    simpl in H.
    unfold sameConstructorTriangleY in H.
    destruct (eqtriangleYDec t1 t2);trivial.
    contradict H.
    apply diff_false_true.
  Qed. 



  Theorem deEqualToOnlyItself: forall (d:Days)(t1:TriangleY), (eqTriangleY d t1 de)=true -> t1=de.
    intros.
    destruct d;destruct t1;trivial;try contradict H;simpl;trivial;compute;intro cont;try (apply (diff_false_true cont)).
  Qed.
  
  
  

  Theorem FCommutesdp0: forall (delt:Delta12) (e:TriangleX), Fe (dp0 delt) (dp0X e) = dp0Y (Ft delt e).
  Proof.
    intros.
    destruct delt;destruct e0;trivial.
  Qed.

  Theorem FCommutesdp1: forall (delt:Delta12) (e:TriangleX), Fe (dp1 delt) (dp1X e) = dp1Y (Ft delt e).
  Proof.
    intros.
    destruct delt;destruct e0;trivial.
  Qed.


  Theorem FCommutesdp2: forall (delt:Delta12) (e:TriangleX), Fe (dp2 delt) (dp2X e) = dp2Y (Ft delt e).
  Proof.
    intros.
    destruct delt;destruct e0;trivial.
  Qed.

  
  
  Theorem FCommutesd0: forall (delt:Delta11) (e:EdgeX), Fv (dv0 delt) (d0X e) = d0Y (Fe delt e).
  Proof.
    intros.
    destruct delt;destruct e0;trivial.     
  Qed.

  Theorem FCommutesd1: forall (delt:Delta11) (e:EdgeX), Fv (dv1 delt) (d1X e) = d1Y (Fe delt e).
  Proof.
    intros.
    destruct delt;destruct e0;trivial.
  Qed.
  
  
  Theorem FCommutesSv: forall (deltp:Delta10) (p:VX), Fe (s deltp) (sX p) = sY (Fv deltp p).
  Proof.
    destruct deltp;destruct p;trivial.
  Qed.

  Theorem FCommutesS0: forall (d:Days) (delt:Delta11) (e:EdgeX), eqTriangleY d (Ft (s0 delt) (se0X e))( se0Y (Fe delt e)) = true.
  Proof.
    intros.
    destruct d;  destruct delt;destruct e0;trivial.
  Qed.

  Theorem FCommutesS1: forall (d:Days) (delt:Delta11) (e:EdgeX), eqTriangleY d (Ft (s1 delt) (se1X e))( se1Y (Fe delt e)) = true.
  Proof.
    intros.
    destruct d;  destruct delt;destruct e0;trivial.
  Qed.


  Definition FCommutesS (Fpoint: Delta10 -> VX -> VY)
             (FEdge: Delta11 -> EdgeX -> EdgeY)
             (FTriangle: Delta12 -> TriangleX -> TriangleY):=
    (forall (deltp:Delta10) (p:VX), FEdge (s deltp) (sX p) = sY (Fpoint deltp p))
    /\ (forall (d:Days) (delt:Delta11) (e:EdgeX),
          eqTriangleY d (FTriangle (s0 delt) (se0X e))( se0Y (FEdge delt e)) = true)
    /\ (forall (d:Days) (delt:Delta11) (e:EdgeX),
          eqTriangleY d (FTriangle (s1 delt) (se1X e))( se1Y (FEdge delt e)) = true).

  Definition FCommutesD (Fpoint: Delta10 -> VX -> VY)
             (FEdge: Delta11 -> EdgeX -> EdgeY)
             (FTriangle: Delta12 -> TriangleX -> TriangleY):=
    (forall (delt:Delta11) (e:EdgeX), Fpoint (dv0 delt) (d0X e) = d0Y (FEdge delt e)) /\
    (forall (delt:Delta11) (e:EdgeX), Fpoint (dv1 delt) (d1X e) = d1Y (FEdge delt e)) /\
    (forall (delt:Delta12) (e:TriangleX), FEdge (dp2 delt) (dp2X e) = dp2Y (FTriangle delt e)) /\
    (forall (delt:Delta12) (e:TriangleX), FEdge (dp1 delt) (dp1X e) = dp1Y (FTriangle delt e)) /\
    forall (delt:Delta12) (e:TriangleX), FEdge (dp0 delt) (dp0X e) = dp0Y (FTriangle delt e).

  Definition FCommutes (Fpoint: Delta10 -> VX -> VY)
             (FEdge: Delta11 -> EdgeX -> EdgeY)
             (FTriangle: Delta12 -> TriangleX -> TriangleY):=
    (FCommutesS Fpoint FEdge FTriangle) /\ (FCommutesD Fpoint FEdge FTriangle).

  Theorem FOrdCommutesS: FCommutesS Fv Fe Ft.
    unfold FCommutesS.
    auto using FCommutesSv, FCommutesS0, FCommutesS1.
  Qed.

  Theorem FOrdCommutesD: FCommutesD Fv Fe Ft.
    unfold FCommutesD.
    auto using FCommutesdp0, FCommutesdp1, FCommutesdp2, FCommutesd0,FCommutesd1.
  Qed.

  Definition Finverse  (FIpoint: Delta10 -> VX -> VY)
             (FIEdge: Delta11 -> EdgeX -> EdgeY)
             (FITriangle: Delta12 -> TriangleX -> TriangleY) :=
    
    (forall (p:VX), FIpoint delta0 p = Fv delta1 p /\
                    FIpoint delta1 p = Fv delta0 p) /\
    (forall (e:EdgeX), FIEdge delta00 e = Fe delta11 e /\
                       FIEdge delta11 e = Fe delta00 e) /\
    (forall (t:TriangleX), FITriangle delta000 t = Ft delta111 t /\
                           FITriangle delta111 t = Ft delta000 t).


  
  (* Verification of:
In day~1 $F^{-}(001,\_)$ would have to map eee:\ntrip{x}{x}{x}{e}{e}{e} to the triangle
$(y_{1},y_{1},y_{0};k,y_{1}y_{0},y_{1}y_{0})$
   *)
  Theorem allFInverseInconsistentEEE: forall  (FIpoint: Delta10 -> VX -> VY)
                                              (FIEdge: Delta11 -> EdgeX -> EdgeY)
                                              (FITriangle: Delta12 -> TriangleX -> TriangleY), Finverse FIpoint FIEdge FITriangle ->
                                                                                               FCommutesS FIpoint FIEdge FITriangle ->
                                                                                               FCommutesD FIpoint FIEdge FITriangle ->
                                                                                               FITriangle delta001 e_e_e = y1y0_y1y0_k.
  Proof.
    intros.
    unfold Finverse in H.
    destruct H.
    destruct H2.
    pose (H2 e).
    destruct  a.         
    assert ((FIEdge delta00 e )=k);auto.
    unfold FCommutesD in H1.
    destruct H1; destruct H7;destruct H8;destruct H9.
    assert (not (y0 = y1)).
    intro.
    discriminate H11.
    assert (dp2Y (FITriangle delta001 e_e_e)=k);auto.
    pose (H8 delta001 e_e_e).
    simpl in e0.
    rewrite H6 in e0;auto.
    assert ((FIpoint delta0 x) = y1).
    apply (H x).
    assert ((FIpoint delta1 x) = y0).        
    apply (H x).
    assert (d0Y (FIEdge delta01 e) =y0).
    pose (H1 delta01 e).
    simpl in e0.
    unfold d0X in e0.
    rewrite H14 in e0;  auto.
    assert (d1Y (FIEdge delta01 e) =y1).
    pose (H7 delta01 e).
    simpl in e0.
    unfold d1X in e0.
    rewrite H13 in e0;  auto.
    assert (( (FIEdge delta01 e)=y1y0)).     
    destruct (FIEdge delta01 e); simpl in H15; simpl in H16; try discriminate H15; try discriminate H16;auto.
    assert (dp1Y (FITriangle delta001 e_e_e)=y1y0);auto.
    pose (H9 delta001 e_e_e);auto.
    simpl in e0.
    rewrite<- e0;auto.
    assert (dp0Y (FITriangle delta001 e_e_e)=y1y0);auto.
    pose (H10 delta001 e_e_e);auto.
    rewrite<- e0;auto.
    destruct (FITriangle delta001 e_e_e); simpl in H12;simpl in H18;simpl in H19; try discriminate H12; try discriminate H18;try discriminate H19;auto.
  Qed.

  (* Verification of $F^{-}(001,sss)=di$ *)
  Theorem allFInverseInconsistentsss: forall  (FIpoint: Delta10 -> VX -> VY)
                                              (FIEdge: Delta11 -> EdgeX -> EdgeY)
                                              (FITriangle: Delta12 -> TriangleX -> TriangleY), Finverse FIpoint FIEdge FITriangle ->
                                                                                               FCommutesS FIpoint FIEdge FITriangle ->
                                                                                               FCommutesD FIpoint FIEdge FITriangle ->
                                                                                               FITriangle delta001 sx_sx_sx = de.
  Proof.
    intros.
    unfold Finverse in H.
    destruct H.
    destruct H2.
    pose (H2 e).
    destruct  a.         
    assert ((FIEdge delta00 e )=k);auto.
    unfold FCommutesD in H1.
    destruct H1; destruct H7;destruct H8;destruct H9.
    assert (not (y0 = y1)).
    intro.
    discriminate H11.
    unfold FCommutesS in H0.
    destruct H0;destruct H12.
    assert ((FIpoint delta1 x) = y0).
    apply H.
    assert ((FIpoint delta0 x) = y1).
    apply H.
    assert (d0Y (FIEdge delta01 sx)=y0).
    pose (H1 delta01 sx).
    simpl in e0;auto.
    rewrite<- e0;auto.
    assert (d1Y (FIEdge delta01 sx)=y1).
    pose (H7 delta01 sx).
    simpl in e0;auto.
    rewrite<- e0;auto.
    assert ((FIEdge delta01 sx)=y1y0);auto.       
    destruct ((FIEdge delta01 sx));simpl in H16;simpl in H17;try discriminate H17; try discriminate H16;auto.
    
    assert (FITriangle delta001 (se0X sx) = se0Y (FIEdge delta01 sx) ).
    
    apply eqTriangleYday1Minimal.
    rewrite H18.
    simpl.
    pose (H12 d1 delta01 sx).
    simpl in e0.
    rewrite H18 in e0.
    destruct (FIEdge delta01 sx);auto.
    rewrite H18 in H19.
    simpl in H19.
    auto.         
  Qed.

  
  (* Verification of  $di \neq (y_{1},y_{1},y_{0};k,y_{1}y_{0},y_{1}y_{0})$ *)
  Theorem deNotEqualToThatOtherEdge: forall (d:Days), (eqTriangleY d  y1y0_y1y0_k de)=false.
  Proof.
    intro.
    destruct d;auto.
  Qed.

  
  Theorem FVRespectsEq: forall (delt:Delta10), unaryFunctionRespectsEquality eqVX  eqVY (Fv delt). 
  Proof.
    unfold unaryFunctionRespectsEquality.
    intros.
    destruct d; destruct elem1;destruct elem2; destruct delt;trivial.
  Qed.
  
  Theorem FERespectsEq: forall (delt:Delta11), unaryFunctionRespectsEquality eqEdgeX  eqEdgeY (Fe delt). 
  Proof.
    unfold unaryFunctionRespectsEquality.
    intros.
    destruct d; destruct elem1;destruct elem2; destruct delt;trivial.
  Qed.

  Theorem FTRespectsEq: forall (delt:Delta12), unaryFunctionRespectsEquality eqTriangleX  eqTriangleY (Ft delt). 
  Proof.
    unfold unaryFunctionRespectsEquality.
    intros.
    destruct d; destruct elem1;destruct elem2; destruct delt;trivial.
  Qed.

  Theorem fill10YProp: forall (d:Days)(e1 e2:EdgeY),  ((eqVY d (d1Y e1) (d1Y e2))=true)->
                                                      (eqEdgeY d (dp1Y (fill10Y e1 e2)) e1)=true /\
                                                      (eqEdgeY d (dp2Y (fill10Y e1 e2)) e2)=true.
  Proof.
    intros.
    split;case d;destruct e1;destruct e2;simpl;trivial.
  Qed.
  
  Theorem fill10YRespectEquality:  binaryFunctionRespectsEquality eqEdgeY eqTriangleY fill10Y.
  Proof.
    unfold binaryFunctionRespectsEquality.
    intros.
    destruct H.
    destruct d;destruct elem1; destruct  elem1p;auto with bool;destruct elem2;destruct elem2p;trivial.
  Qed.

  Theorem fill11YRespectEquality:  binaryFunctionRespectsEquality eqEdgeY eqTriangleY fill11Y.
  Proof.
    unfold binaryFunctionRespectsEquality.
    intros.
    destruct H.
    destruct d;destruct elem1; destruct  elem1p;auto with bool;destruct elem2;destruct elem2p;trivial.
  Qed.

  Theorem fill11YProp: forall (d:Days)(e1 e2:EdgeY),  ((eqVY d (d1Y e1) (d0Y e2))=true)->
                                                      (eqEdgeY d (dp0Y (fill11Y e1 e2)) e1)=true /\
                                                      (eqEdgeY d (dp2Y (fill11Y e1 e2)) e2)=true.
  Proof.
    intros.
    split;destruct d;destruct e1;destruct e2;trivial.
  Qed.


  Theorem fill12YRespectEquality:  binaryFunctionRespectsEquality eqEdgeY eqTriangleY fill12Y.
  Proof.
    unfold binaryFunctionRespectsEquality.
    intros.
    destruct H.
    destruct d;destruct elem1; destruct  elem1p;auto with bool;destruct elem2;destruct elem2p;trivial.
  Qed.

  Theorem fill12YProp: forall (d:Days)(e0 e1:EdgeY),  ((eqVY d (d0Y e0) (d0Y e1))=true)->  (eqEdgeY d (dp0Y (fill12Y e0 e1)) e0)=true /\
                                                                                           (eqEdgeY d (dp1Y (fill12Y e0 e1)) e1)=true.
  Proof.
    intros.
    split;destruct d;destruct e0;destruct e1;trivial.
  Qed.


  
  
  Theorem fill20YProp: forall (d:Days)(t1 t2 t3:TriangleY),  (eqEdgeY d (dp1Y t1) (dp1Y t2))=true /\
                                                             (eqEdgeY d (dp2Y t1) (dp1Y t3))=true /\
                                                             (eqEdgeY d (dp2Y t2) (dp2Y t3))=true ->
                                                             (
                                                               (eqEdgeY d (dp0Y t1) (dp0Y (fill20Y t1 t2 t3)))=true /\
                                                               (eqEdgeY d (dp0Y t2) (dp1Y (fill20Y t1 t2 t3)))=true   /\
                                                               (eqEdgeY d (dp0Y t3) (dp2Y (fill20Y t1 t2 t3)))=true).
  Proof.
    intros.
    destruct H.
    destruct H0.
    destruct d.
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).        
  Qed.

  Definition eqTriangleYreflexive := proj1 YModel_obligation_3.
  Definition eqTriangleYTrans := proj2 (proj2 YModel_obligation_3).
  

  Lemma fill20YRespectsEqualty1: forall (d:Days)(t1 t2 t3:TriangleY) (t1p:TriangleY),
                                   (eqTriangleY d t1 t1p)=true -> (eqTriangleY d (fill20Y t1 t2 t3) (fill20Y t1p t2 t3))=true.
    
    destruct d.     
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill20YRespectsEqualty1.

  Lemma fill20YRespectsEqualty2: forall (d:Days)(t1 t2 t3:TriangleY) (t2p:TriangleY),
                                   (eqTriangleY d t2 t2p)=true -> (eqTriangleY d (fill20Y t1 t2 t3) (fill20Y t1 t2p t3))=true.
    intros.
    destruct d.
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t1; (trivial using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill20YRespectsEqualty2.
  
  Lemma fill20YRespectsEqualty3: forall (d:Days)(t1 t2 t3:TriangleY) (t3p:TriangleY),
                                   (eqTriangleY d t3 t3p)=true -> (eqTriangleY d (fill20Y t1 t2 t3) (fill20Y t1 t2 t3p))=true.
    intros.
    destruct d.
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t1;trivial. 
  Qed.
  Hint Resolve fill20YRespectsEqualty3.


  Theorem fill20YRespectsEqualty:  tertaryFunctionRespectsEquality eqTriangleY eqTriangleY fill20Y.
  Proof.
    apply TertaryFunctionRespectsEqualtyPointwise;auto.
    apply YModel_obligation_3.
  Qed.


  
  Theorem fill21YProp: forall (d:Days)(t1 t2 t3:TriangleY),
                         (eqEdgeY d (dp1Y t1) (dp0Y t2))=true /\
                         (eqEdgeY d (dp2Y t1) (dp0Y t3))=true /\
                         (eqEdgeY d (dp2Y t2) (dp2Y t3))=true ->
                         ((eqEdgeY d (dp0Y t1) (dp0Y (fill21Y t1 t2 t3)))=true /\
                          (eqEdgeY d (dp1Y t2) (dp1Y (fill21Y t1 t2 t3)))=true  /\
                          (eqEdgeY d (dp1Y t3) (dp2Y (fill21Y t1 t2 t3)))=true).
  Proof.
    intros.
    destruct H.
    destruct H0.
    destruct d.
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).
  Qed.
  
  Lemma fill21YRespectsEqualty1: forall (d:Days)(t1 t2 t3:TriangleY) (t1p:TriangleY),
                                   (eqTriangleY d t1 t1p)=true -> (eqTriangleY d (fill21Y t1 t2 t3) (fill21Y t1p t2 t3))=true.
    intros.
    destruct d.
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill21YRespectsEqualty1.

  Lemma fill21YRespectsEqualty2: forall (d:Days)(t1 t2 t3:TriangleY) (t2p:TriangleY),
                                   (eqTriangleY d t2 t2p)=true -> (eqTriangleY d (fill21Y t1 t2 t3) (fill21Y t1 t2p t3))=true.
    intros.
    destruct d.
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t1; (auto using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill21YRespectsEqualty2.

  Lemma fill21YRespectsEqualty3: forall (d:Days)(t1 t2 t3:TriangleY) (t3p:TriangleY),
                                   (eqTriangleY d t3 t3p)=true -> (eqTriangleY d (fill21Y t1 t2 t3) (fill21Y t1 t2 t3p))=true.
    intros.
    destruct d.
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (auto using eqTriangleYreflexive) ;destruct t1;trivial. 
  Qed.
  Hint Resolve fill21YRespectsEqualty3.

  Theorem fill21YRespectsEqualty:  tertaryFunctionRespectsEquality eqTriangleY eqTriangleY fill21Y.
Proof.
    apply TertaryFunctionRespectsEqualtyPointwise;auto.
    apply YModel_obligation_3.
  Qed.
  
  Theorem fill22YProp: forall (d:Days)(t1 t2 t3:TriangleY),
                         (eqEdgeY d (dp0Y t1) (dp0Y t2))=true /\
                         (eqEdgeY d (dp2Y t1) (dp0Y t3))=true /\
                         (eqEdgeY d (dp2Y t2) (dp1Y t3))=true ->
                         ((eqEdgeY d (dp1Y t1) (dp0Y (fill22Y t1 t2 t3)))=true /\
                          (eqEdgeY d (dp1Y t2) (dp1Y (fill22Y t1 t2 t3)))=true  /\
                          (eqEdgeY d (dp2Y t3) (dp2Y (fill22Y t1 t2 t3)))=true).
  Proof.
    intros.
    destruct H.
    destruct H0.
    destruct d.
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]). 
  Qed.
  
  Lemma fill22YRespectsEqualty1: forall (d:Days)(t1 t2 t3:TriangleY) (t1p:TriangleY),
                                   (eqTriangleY d t1 t1p)=true -> (eqTriangleY d (fill22Y t1 t2 t3) (fill22Y t1p t2 t3))=true.
    intros.
    destruct d.
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill22YRespectsEqualty1.

  Lemma fill22YRespectsEqualty2: forall (d:Days)(t1 t2 t3:TriangleY) (t2p:TriangleY),
                                   (eqTriangleY d t2 t2p)=true -> (eqTriangleY d (fill22Y t1 t2 t3) (fill22Y t1 t2p t3))=true.
    intros.
    destruct d.
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t1; (auto using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill22YRespectsEqualty2.
  
  Lemma fill22YRespectsEqualty3: forall (d:Days)(t1 t2 t3:TriangleY) (t3p:TriangleY),
                                   (eqTriangleY d t3 t3p)=true -> (eqTriangleY d (fill22Y t1 t2 t3) (fill22Y t1 t2 t3p))=true.
    intros.
    destruct d.
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t1;trivial. 
  Qed.
  Hint Resolve fill22YRespectsEqualty3.
  

  Theorem fill22YRespectsEqualty:  tertaryFunctionRespectsEquality eqTriangleY eqTriangleY fill22Y.
  Proof.
    apply TertaryFunctionRespectsEqualtyPointwise;auto.
    apply YModel_obligation_3.
  Qed.

  Theorem fill23YProp: forall (d:Days)(t1 t2 t3:TriangleY),
                         (eqEdgeY d (dp0Y t1) (dp0Y t2))=true /\
                         (eqEdgeY d (dp1Y t1) (dp0Y t3))=true /\
                         (eqEdgeY d (dp1Y t2) (dp1Y t3))=true ->
                         ((eqEdgeY d (dp2Y t1) (dp0Y (fill23Y t1 t2 t3)))=true /\
                          (eqEdgeY d (dp2Y t2) (dp1Y (fill23Y t1 t2 t3)))=true  /\
                          (eqEdgeY d (dp2Y t3) (dp2Y (fill23Y t1 t2 t3)))=true) .
  Proof.
    intros.
    destruct H.
    destruct H0.
    destruct d.
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).
    destruct t1;destruct t2;destruct t3; (split; [trivial | split;trivial]).
  Qed.
  
  Lemma fill23YRespectsEqualty1: forall (d:Days)(t1 t2 t3:TriangleY) (t1p:TriangleY),
                                   (eqTriangleY d t1 t1p)=true -> (eqTriangleY d (fill23Y t1 t2 t3) (fill23Y t1p t2 t3))=true.
    destruct d.
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t1; destruct  t1p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill23YRespectsEqualty1.

  Lemma fill23YRespectsEqualty2: forall (d:Days)(t1 t2 t3:TriangleY) (t2p:TriangleY),
                                   (eqTriangleY d t2 t2p)=true -> (eqTriangleY d (fill23Y t1 t2 t3) (fill23Y t1 t2p t3))=true.
    destruct d.
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t2; destruct  t2p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t1; (trivial using eqTriangleYreflexive) ;destruct t3;trivial. 
  Qed.
  Hint Resolve fill23YRespectsEqualty2.

  Lemma fill23YRespectsEqualty3: forall (d:Days)(t1 t2 t3:TriangleY) (t3p:TriangleY),
                                   (eqTriangleY d t3 t3p)=true -> (eqTriangleY d (fill23Y t1 t2 t3) (fill23Y t1 t2 t3p))=true.
    destruct d.
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);trivial.        
    destruct t3; destruct  t3p;(auto  with bool || trivial using eqTriangleYreflexive);destruct t2; (trivial using eqTriangleYreflexive) ;destruct t1;trivial. 
  Qed.
  Hint Resolve fill23YRespectsEqualty3.


  Theorem fill23YRespectsEqualty:  tertaryFunctionRespectsEquality eqTriangleY eqTriangleY fill23Y.
Proof.
    apply TertaryFunctionRespectsEqualtyPointwise;auto.
    apply YModel_obligation_3.
  Qed.

  Program  Instance YModelFill :  fillableModel  := {|
                                                     fill10:=fill10Y;
                                                     fill11:=fill11Y;
                                                     fill12:=fill12Y;
                                                     fill20:=fill20Y;
                                                     fill21:=fill21Y;
                                                     fill22:=fill22Y;
                                                     fill23:=fill23Y
                                                   |}.
  Solve All Obligations using (auto using fill20YProp, fill20YRespectsEqualty, fill21YProp, fill21YRespectsEqualty, fill22YProp, fill22YRespectsEqualty, fill23YProp, fill23YRespectsEqualty).

  Solve All Obligations using (autounfold; repeat split;autounfold;intros;(destructGroundElement VY EdgeY TriangleY);trivial;destruct H;destruct H0;trivial).



End KripkeModel.