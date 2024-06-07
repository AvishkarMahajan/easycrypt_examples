require import Bool Int Real Distr DInterval.
require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.

op indFn (i j x : int) : real = if (i = j /\ x <> 1) then 1.0 else 0.0.


op geomPot (n c : int) (x : int) : real = if x <> 1 then (if n = c then 1.0 else 0.0) else (if (c <= n /\ x = 1) then 0.5 * (0.5^(n - c)) else 0.0).

lemma potIneq : forall (i c x : int), (indFn i c x)%pos <= (geomPot i c x)%pos.
    proof. admitted.

    op hGeom (i c x : int) : real = if (x = 1 /\ c = i) then 0.0 else (if (x <> 1 /\ c = i) then 1.0 else 2.0 * geomPot i c x).

lemma hIneq : forall (i c : int), Ep [0..1] (fun (x : int) => (hGeom i c x)%xr) <=
    (geomPot i c 1)%xr.
 proof. admitted. (* move => i c. case (i = c). move => H.
rewrite H.  rewrite /geomPot. simplify. rewrite/Ep. rewrite /hGeom. simplify. auto. rewrite/geomPot. progress. auto. simplify.  admitted.*)    
    
    


module Geom = {
var i : int
var c : int
var x : int  
proc f() : unit = {
    while (x = 1)
    {x <$ [0..1];
      if (x = 1) {c <- c + 1;} else {c <- c;}}}}.

  ehoare geomDist : Geom.f : (Geom.c = 0 /\ Geom.x = 1) `|` ((0.5^(Geom.i + 1))%xr) ==> (indFn Geom.i (Geom.c) Geom.x)%xr.
proof. proc.
  while (((geomPot Geom.i Geom.c Geom.x))%xr). progress.
  case (Geom.x{hr} = 1). smt.  smt. seq 1 : (((hGeom Geom.i Geom.c Geom.x))%xr). rnd. skip. progress.  simplify. case (Geom.x{hr} = 1). simplify. move => H.  rewrite H. apply hIneq. smt. auto. smt. skip. progress.  case (Geom.c{hr} = 0). case (Geom.x{hr} = 1).
move => H. move => H'. rewrite H. rewrite H'. simplify. smt. smt. smt. qed.

 

op randomWalkDist (s y : int) : xreal.

op indFnR (c n s : int) : real = if (c = n /\ s = 0) then 1.0 else 0.0.

axiom rwProp1: forall (s y : int),
    (s = 0 /\ y = 0) => randomWalkDist s y = 1.0%xr.

axiom rwProp2: forall (s y : int),
      (0 < s /\ y = 0) => randomWalkDist s y = 0.0%xr.
      
axiom rwProp3 :  forall (s y : int),
      (s = 0 /\ 0 < y) => randomWalkDist s y = 0.0%xr.

axiom rwProp4: forall (s y : int),
(0 < s /\ 0 < y) => randomWalkDist s y = (0.5%xr * randomWalkDist (s + 1) (y - 1) + 0.5%xr* randomWalkDist (s - 1) (y - 1)).

op rwalkPot (c n s : int) : xreal.
(*op xrwalkPot (c n s : int) (x : bool) : xreal = if (x = true /\ 0 < s /\  0 < (n - c)) then 2.0%xr * rwalkPot c  n s  else (if (x = false /\ 0 < s /\ 0 < (n - c)) then rwalkPot (c + 1) n (s - 1) else 0.0%xr).*)

lemma helper: forall (c n s : int),
Ep {0,1}
  (fun (_ : bool) =>
     2%xr * rwalkPot c n s) <=
    rwalkPot c n s.
proof. admitted.

lemma helper2 : forall (c n s : int),
0 < s =>     
rwalkPot (c + 1) n (s + 1) <=
    2%xr * rwalkPot c n s.
proof.
  admitted.

lemma helper3 : forall (c n s : int),
0 < s =>     
rwalkPot (c + 1) n (s - 1) <=
    2%xr * rwalkPot c n s.
proof. admitted.
  






axiom rwP1 : forall (c n s: int),
s = 0 /\ c = n => rwalkPot c n s = 1.0%xr.

axiom rwP2 : forall (c n s: int),
s = 0 /\ c <> n => rwalkPot c n s = 0.0%xr.

axiom rwP3 : forall (c n s :int),
  n < c => rwalkPot c n s = 0.0%xr.

axiom rwP4 : forall (c n s : int),
  c <= n /\ 0 < s => rwalkPot c n s = randomWalkDist s (n - c).

lemma rwP4' : forall (n s : int),
   0 < s => rwalkPot 0 n s <= randomWalkDist s n.
proof. admitted.






module RndWalk = {
var s : int
var c : int
var x : bool
var n : int  
proc f() : unit = {
    while (0 < s)
    {x <$ {0,1};
      if (x = true) {s <- s + 1; c <- c + 1;} else {s <- s - 1; c <- c + 1;}
}}}.

ehoare geomDist : RndWalk.f : ((0 < RndWalk.s) /\ (RndWalk.c = 0)) `|` (randomWalkDist RndWalk.s RndWalk.n) ==> (indFnR RndWalk.c (RndWalk.n) RndWalk.s)%xr.
proof. proc.
  while (rwalkPot RndWalk.c RndWalk.n RndWalk.s). smt. seq 1 : ((0 < RndWalk.s) `|` (2.0%xr * rwalkPot RndWalk.c RndWalk.n RndWalk.s)). rnd. skip. progress. case (0 < RndWalk.s{hr}). simplify. move => H. apply helper.
  smt. auto. progress. case (RndWalk.x{hr} = true). move => H. case (0 < RndWalk.s{hr}). move => H'. simplify. apply helper2. assumption. smt. move => H. case (0 < RndWalk.s{hr}). move => H'. simplify. apply helper3. assumption. smt. skip. progress. case (0 < RndWalk.s{hr}). move => H. simplify. case (RndWalk.c{hr} = 0). move => H'. simplify. rewrite H'. apply rwP4'. assumption. smt. smt. 





 
 



