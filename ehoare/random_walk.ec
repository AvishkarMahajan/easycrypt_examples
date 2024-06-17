require import Bool Int Real Distr DInterval.
require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.
require import ExpVal.




op randomWalkDist (s y : int) : real.

op indFnR (c n s : int) : real = if (0 <= n /\c = n /\ s = 0) then 1.0 else 0.0.

axiom rwProp1: forall (s y : int),
    (s = 0 /\ y = 0) => randomWalkDist s y = 1.0.

axiom rwProp2: forall (s y : int),
      (0 < s /\ y = 0) => randomWalkDist s y = 0.0.
      
axiom rwProp3 :  forall (s y : int),
      (s = 0 /\ 0 < y) => randomWalkDist s y = 0.0.

axiom rwProp4: forall (s y : int),
(0 < s /\ 0 < y) => randomWalkDist s y = (0.5 * randomWalkDist (s + 1) (y - 1) + 0.5* randomWalkDist (s - 1) (y - 1)).

axiom rwProp5 : forall (s y : int), (s < 0 \/ y < 0) => randomWalkDist s y = 0.0.

axiom rwPos : forall (s y : int), 0.0 <= randomWalkDist s y. (*can prove via induction : proof. progress. case (s < 0). move => H.  rewrite rwProp5. smt. smt. case (y < 0). progress. rewrite rwProp5. smt. smt. progress. case (s = 0). progress. case (y = 0). progress. rewrite rwProp1. smt. smt. progress. rewrite rwProp3. smt. smt. progress...*)

op rwalkPot (c n s : int) : real.


 

axiom rwP3 : forall (c n s :int),
  0 <=n /\ n < c => rwalkPot c n s = 0.0.

axiom rwP4 : forall (c n s : int),
  0 <= n /\ c <= n => rwalkPot c n s = randomWalkDist s (n - c).

lemma rwP4' : forall (n s : int),
   0 <= n /\ 0 < s  => rwalkPot 0 n s <= randomWalkDist s n.
    proof. progress. rewrite rwP4. auto. simplify. auto.
  qed.
 



    op hrand (c n s :int) (x : bool) : real = if 0 <= n then (if s = 0 then 0.0 else (if  x = true then rwalkPot (c +1) n (s + 1) else rwalkPot (c + 1) n (s - 1))) else 0.0.

  lemma helper5 : forall (c n s : int), 0 <= n /\ 0 < s => Ep {0,1} (fun (x : bool) => (if x = true then rwalkPot (c + 1) n (s + 1) else rwalkPot (c + 1) n (s -1))%xr) = (rwalkPot c n s)%xr. proof. progress. rewrite L4. case (n < c).
      move => H'. rewrite rwP3. smt. simplify. rewrite rwP3. smt. rewrite rwP3. smt. smt. case (n = c). move => H1. move => H2. simplify. rewrite rwP3. smt. rewrite rwP3. smt. rewrite rwP4. smt. rewrite H1. simplify. rewrite rwProp2. smt. smt. move => H1. move => H2. rewrite rwP4. smt. simplify. rewrite rwP4. smt. rewrite rwP4. smt. rewrite (rwProp4 s).  smt. rewrite/inv.  simplify. rewrite divBy2. progress. apply rwPos. apply rwPos. smt. qed. (*rewrite using rwProp4 in 3rd term. remaining can be solved using smt.*) 



lemma helper6 : forall (c n : int), 0 <= n => (indFnR c n 0) = (rwalkPot c n 0). proof.  progress. rewrite/indFnR. rewrite/rwalkPot. case (c = n). move => H'. rewrite rwP4.
smt. simplify. rewrite H'. simplify. rewrite rwProp1.
smt. smt. progress. case (n < c). move => H''. rewrite rwP3. smt. smt. move => H'. rewrite rwP4. smt. rewrite rwProp3. smt. smt. qed.




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

ehoare rndWalk : RndWalk.f : ((0 <= RndWalk.n /\ 0 < RndWalk.s) /\ (RndWalk.c = 0)) `|` (randomWalkDist RndWalk.s RndWalk.n)%xr ==> (indFnR RndWalk.c (RndWalk.n) RndWalk.s)%xr.
proof. proc.
  while ((0 <= RndWalk.n) `|` (rwalkPot RndWalk.c RndWalk.n RndWalk.s)%xr). progress. case (RndWalk.s{hr} = 0). progress. case (0 <= RndWalk.n{hr}). progress. rewrite helper6. smt.  smt.  smt. progress. smt.  seq 1 : ((0 <= RndWalk.n /\ 0 < RndWalk.s) `|` (hrand RndWalk.c RndWalk.n RndWalk.s RndWalk.x)%xr). rnd. skip. progress. case (0 < RndWalk.s{hr}). simplify. move => H. rewrite/hrand.  simplify.  case (RndWalk.s{hr} = 0). move => H'.  smt. move => H'. case (0 <= RndWalk.n{hr}). move => H''. simplify.  rewrite helper5.  smt. smt. smt. smt.
  auto. progress. case (RndWalk.x{hr} = true). move => H''. smt. smt. auto. progress.  case (0 < RndWalk.s{hr}). move => H'. simplify. rewrite/hrand. case (RndWalk.x{hr} = true). simplify. case (0 < RndWalk.s{hr}). progress.  case (0 <= RndWalk.n{hr}). smt. smt. smt. smt.  smt.
qed.

(*    (*progress. case (0 < RndWalk.s{hr}). rewrite/hrand. smt. smt.*) skip. progress. case (0 < RndWalk.s{hr}). move => H. simplify. case (RndWalk.c{hr} = 0). move => H'. simplify. rewrite H'.  case (0 <= RndWalk.n{hr}). simplify. move => H''.  rewrite rwP4. smt. smt. smt. smt. smt. qed. *) 





 
 


