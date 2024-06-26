require import AllCore.
require import Bool Int Real.

require import  Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.
require import ExpVal.




op binDist (m n c : int) : real. (* This functions represents the probability that given the current value of the binomial variable is n, then in c more steps it will reach the vaalue m*)

op indFnB (m n c  : int) : real = if (m = n /\ c = 0) then 1.0 else 0.0.

axiom binProp1: forall (m n c : int),
    (m < n) => binDist m n c = 0.0.

axiom binProp2: forall (m n c : int),
      (m <> n /\ c = 0) => binDist m n c = 0.0.
      
axiom binProp3 :  forall (m n c : int),
      (m = n /\ c = 0) => binDist m n c = 1.0.

axiom binProp4: forall (m n c : int),
0 < c => binDist m n c = 0.0.

axiom binProp5 : forall (m n c : int), 0 < c => binDist m n c = 0.5 * binDist m n (c -1) + 0.5 * binDist m (n + 1) (c -1).

axiom binPos : forall (m n c : int), 0.0 <= binDist m n c.

lemma helper : forall (m n c : int), 0 < c /\ 0 <= m /\ 0 <= n => Ep {0,1}
  (fun (x : bool) =>
     if x = true then (binDist m (n + 1) (c - 1))%xr
     else (binDist m n (c - 1))%xr) <=
(binDist m n c)%xr. proof. admitted. (*apply binProp5*)







module Bin = {
var m : int
var c : int
var x : bool
var n : int  
proc f() : unit = {
n <- 0;    
    while (0 < c)
    {x <$ {0,1};
      if (x = true) {n <- n + 1; c <- c - 1;} else {c <- c - 1;}
}}}.

ehoare bin : Bin.f : ((0 <= Bin.m) /\ (0 < Bin.c)) `|` (binDist Bin.m 0 Bin.c)%xr ==> (indFnB Bin.m Bin.n Bin.c)%xr.
proof. proc. seq 1 :  ((0 <= Bin.m /\ 0 < Bin.c /\ Bin.n = 0) `|` (binDist Bin.m 0 Bin.c)%xr). auto. while ((0 <= Bin.m /\ 0 <= Bin.n) `|` (binDist Bin.m Bin.n Bin.c)%xr). progress. case (Bin.m{hr} = Bin.n{hr}). move => H. case (Bin.c{hr} = 0). move => H'. rewrite binProp3. smt. rewrite/indFnB. rewrite H. rewrite H'. simplify. smt. rewrite/indFnB. simplify. move => H'. smt. smt.
seq 1 : ( (0 < Bin.c) `|`
  ((0 <= Bin.m /\ 0 <= Bin.n) `|` (if Bin.x = true then (binDist Bin.m (Bin.n + 1) (Bin.c -1))%xr else (binDist Bin.m Bin.n (Bin.c - 1))%xr))). rnd. skip. progress. case ((0 < Bin.c{hr} /\ 0 <= Bin.m{hr} /\ 0 <= Bin.n{hr})).  move => H. simplify. apply helper. smt. smt. progress. auto. smt.  auto. smt. qed.
  


 
 


