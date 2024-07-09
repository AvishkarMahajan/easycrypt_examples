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
 
op indFnD (m k y : int) : real = if (1 <= m /\ 0 <= k /\ k <= 2*m -1) then (if k = y then 1.0 else 0.0) else 0.0.

lemma helper3 : forall (m k : int), (1 <= m /\
   0 <= k /\ k <= 2 * m - 1) => Ep [0..1]
  (fun (x : int) =>
     Ep [0..m - 1]
       (fun (y : int) =>
          (indFnD m k (2 * y + x))%xr)) <=
(inv (2 * m)%rp)%xr. proof. admitted. (* Every k corresponds to a unique pair (x,y) satisfying the equation k = 2*y + x and vice versa. Since x,y come from independent distributions, the corresponding probability is 1/2m.*)

module Doub_rng = {
var m : int
var y : int
var x : int  
var k : int  
proc f() : unit = {
    
  x <$ [0..1];
  y <$ [0..(m - 1)];  
  y <- (2 * y) + x;  
      
}}.



ehoare doub : Doub_rng.f : (((1 <= Doub_rng.m) /\ (0 <= Doub_rng.k)/\ Doub_rng.k <= (2*Doub_rng.m - 1)) `|` (1.0%xr/(2*Doub_rng.m)%xr )) ==> (indFnD Doub_rng.m Doub_rng.k Doub_rng.y)%xr.
proof. proc. wp.  auto. progress.  case ( (1 <= Doub_rng.m{hr} /\
  0 <= Doub_rng.k{hr} /\ Doub_rng.k{hr} <= 2 * Doub_rng.m{hr} - 1)). move => H. simplify. apply helper3. smt. smt. qed.

(*
FDR (n) =
v <- 1; c <- 0;

-- While  (v < n or c >= n):
If (v < n) :

v <- 2v;
c <- 2c + flip()

else:

v <- v -n ;
c <- c - n ;

v <- 2v ;
  c <- 2c + flip() -- *)

(* Fix starting memory values k, n, v, c) then let p(k,n,v,c) be the probability that after executing the program enclosed in (--) we have c = k 

(k, n are fixed throughout)

We have the following reccurence relations

if v >= n and c < n then, if c = k then p (k n v c) = 1.0 else 0.0

if v < n then p(k n v c) = 0.5* p(k n 2v 2c) + 0.5*p(k n 2v 2c + 1)

if v > = n and c >= n then p(k n v c) = 0.5 * p(k n (2v - 2n) (2c - 2n)) + 0.5* p(k n (2v -2n) (2c -2n + 1)).

forall k n v c, 0<= p(k n v c)

      
For any function h satisfying the above axioms eHoare can prove that prob(c = k) at the end of the program is such that prob(c = k) <= h(k n 0 1)

Since p is a probability and the loop is AST we know that p(0,n,1,0) + p(1,n,1,0)+...+p(n-1,n,1,0) = 1.0.
 
From all the above constraints  does it follow that p(k,n,1,0) <= 1/n if k<n and 0 if k>=n?


Similar axioms can be generated for distribution of runtime of the program. *)








