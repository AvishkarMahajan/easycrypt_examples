require import AllCore.
require import Bool Int Real.

require import  Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.
require import ExpVal.





op indFnU (n k x  : int) : real = if (0 <= n /\ k <= n /\ 0<= k /\ x = k) then 1.0 else 0.0.
op UnifDist_n (n k x : int): real = if (0 <= n /\ 0 <= k /\ k <= n /\ n < x) then 1.0/(n%r + 1.0) else (if x = k then 1.0 else 0.0).

lemma helper: forall (n m k  : int), (0 < m /\
    0 <= n /\
    n <= m /\ 0 <= k
/\ k <= n ) => Ep [0..m]
  (fun (x : int) =>
     (if n < x then inv (n%r + 1%r)
      else b2r (x = k))%xr) <=
   (inv (n%r + 1%r))%xr. proof. admitted.

     (* p = 1/(m + 1) + ((m-n)/m+1) * p => (n + 1 / m + 1)*p = 1/ m + 1 => p = 1 / n + 1*)

lemma helper2 : forall (m : int), 0 < m => Ep [0..m] (fun (_ : int) => 0%xr) <= 0%xr.
proof. admitted.








module CondUnif = {
var m : int
var n : int
var x : int
var k : int  
proc f() : unit = {
     while (n < x)
    {x <$ [0..m];
      
}}}.

ehoare condUnif : CondUnif.f : ((0 < CondUnif.m) /\ (0 <= CondUnif.n)/\ CondUnif.n <= CondUnif.m /\ 0 <= CondUnif.k) `|` (UnifDist_n CondUnif.n CondUnif.k CondUnif.x )%xr ==> (indFnU CondUnif.n CondUnif.k CondUnif.x)%xr.
proof. proc. while (((0 < CondUnif.m) /\ (0 <= CondUnif.n)/\ CondUnif.n <= CondUnif.m /\ 0 <= CondUnif.k) `|` (if (0 <= CondUnif.k /\ CondUnif.k <= CondUnif.n) then (if CondUnif.n < CondUnif.x then  1.0/(CondUnif.n%r + 1.0) else (if CondUnif.x = CondUnif.k then 1.0 else 0.0)) else  0.0)%xr). auto. progress. case (CondUnif.n{hr} < CondUnif.x{hr}). smt. move => H. simplify. smt. rnd. auto. auto. progress.  case (CondUnif.n{hr} < CondUnif.x{hr}).
 move => H. simplify. case (0 < CondUnif.m{hr} /\
 0 <= CondUnif.n{hr} /\
 CondUnif.n{hr} <= CondUnif.m{hr} /\ 0 <= CondUnif.k{hr}). move => H'.  
rewrite H'. simplify. case (CondUnif.k{hr} <= CondUnif.n{hr}). move => H''. apply helper. smt. move => H''. auto.  apply helper2. smt. smt. smt. auto.  progress. case (0 < CondUnif.m{hr} /\
 0 <= CondUnif.n{hr} /\
 CondUnif.n{hr} <= CondUnif.m{hr} /\ 0 <= CondUnif.k{hr}).
 move => H. simplify. smt. smt. qed. 
 

(*
FDR (n) =
v <- 1; c <- 0;

While  (v < n or c >= n):
If (v < n) :

v <- 2v;
c <- 2c + flip()

else:

v <- v -n ;
c <- c - n ;

v <- 2v ;
c <- 2c + flip() *)


