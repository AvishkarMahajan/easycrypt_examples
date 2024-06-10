require import Bool Int Real Distr DInterval.
require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.


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

ehoare rndWalk : RndWalk.f : ((0 < RndWalk.s) /\ (RndWalk.c = 0)) `|` (randomWalkDist RndWalk.s RndWalk.n) ==> (indFnR RndWalk.c (RndWalk.n) RndWalk.s)%xr.
proof. proc.
  while (rwalkPot RndWalk.c RndWalk.n RndWalk.s). smt. seq 1 : ((0 < RndWalk.s) `|` (2.0%xr * rwalkPot RndWalk.c RndWalk.n RndWalk.s)). rnd. skip. progress. case (0 < RndWalk.s{hr}). simplify. move => H. apply helper.
  smt. auto. progress. case (RndWalk.x{hr} = true). move => H. case (0 < RndWalk.s{hr}). move => H'. simplify. apply helper2. assumption. smt. move => H. case (0 < RndWalk.s{hr}). move => H'. simplify. apply helper3. assumption. smt. skip. progress. case (0 < RndWalk.s{hr}). move => H. simplify. case (RndWalk.c{hr} = 0). move => H'. simplify. rewrite H'. apply rwP4'. assumption. smt. smt. qed. 





 
 



