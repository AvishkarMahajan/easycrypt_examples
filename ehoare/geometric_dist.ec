(* Need to have expVal.ec in buffer *)
require import Bool Int Real Distr DInterval.
require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.


op indFn (i j x : int) : real = if (i = j /\ x <> 1) then 1.0 else 0.0.

op geomPot (n c : int) (x : int) : real = if x <> 1 then (if n = c then 1.0 else 0.0) else (if (c <= n /\ x = 1) then 0.5 * (0.5^(n - c)) else 0.0).

lemma potIneq : forall (i c x : int), (indFn i c x)%pos <= (geomPot i c x)%pos.
    proof. rewrite /indFn. rewrite/geomPot. progress. smt. qed. 
      

    op hGeom (i c x : int) : real = if (x = 1 /\ c = i) then 0.0 else (if (x <> 1 /\ c = i) then 1.0 else 2.0 * geomPot i c x).

lemma hIneq : forall (i c : int), Ep [0..1] (fun (x : int) => (hGeom i c x)%xr) <=
    (geomPot i c 1)%xr.
 proof. progress. rewrite L3. rewrite/hGeom. rewrite/ geomPot. smt. qed.  
    


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
