require import Bool Int Real Distr DInterval.
require import AllCore Distr List DInterval StdOrder.
require import Array.
require import Xreal.
import StdBigop.Bigreal.
import StdBigop.Bigint.
require import ExpVal.

op update (l : 'a list) (pos : int) (k : 'a) : 'a list = 
  List.mapi (fun i x => if i = pos then k else x) l.

op size (l : 'a list) : int =
with l = [] => 0
with l = x :: xs => 1 + size xs.

op mkzeros (n : int) : int list. 

axiom mz1 : forall (n : int), n <= 0 => mkzeros n = [].
axiom mz2 : forall (n : int), 0 < n => mkzeros n = 0 :: mkzeros (n -1).

op sumToN (n : int) (f : int -> real) : real.

op hasZero (l : int list) : bool =
with l = [] => false
with l = x :: xs => if x = 0 then true else hasZero xs.

op count1 (l : int list) : int =
with l = [] => 0
with l = x :: xs => if x = 1 then (1 + count1 xs) else count1 xs.

op count0 (l : int list) : int =
with l = [] => 0
with l = x :: xs => if x = 0 then (1 + count0 xs) else count0 xs.


op ccDist (n c d : int) : real. (*This function represents the probability that given there are n distinct coupons initially, and currently one has obtained c distinct coupons then after d further  draws, and no less, one will obtain all  n distinct coupons*)

axiom ccd1 : forall (n  d : int), (0 < n /\ !(d = 0))  => ccDist n n d = 0.0.
axiom ccd2 : forall (n c : int), 0 < n /\ n = c => ccDist n c 0 = 1.0.
axiom ccd3 : forall (n c d: int), (0 < n /\ d < n - c) => ccDist n c d = 0.0.
axiom ccd4 : forall (n c d :int), (0 < n /\ n < c) => ccDist n c d = 0.0.
axiom ccd5 : forall (n c d : int), (0 < n /\ c <= n) => ccDist n c d = (c%r/n%r)* ccDist n c (d - 1) + ((n-c)%r/n%r)*ccDist n (c + 1) (d - 1). 
axiom ccd6 : forall (n c d : int), (n <=0) => ccDist n c d = 0.0.
axiom cc7 : forall (n c d : int), 0.0 <= ccDist n c d.


op isBits (l : int list): bool =
with l = [] => true
with l = x :: xs => if !(x = 0 \/ x = 1) then false else isBits xs.

lemma helper : forall (l : int list), ! hasZero l => count0 l = 0. proof. admitted.
lemma helper2 : forall (n c m k : int) (ys : int list),
0 < n /\
   n <= m /\
   c = count1 ys /\
   count1 ys + count0 ys = n /\ hasZero ys /\ 0 <= k => Ep [1..n]
  (fun (x : int) =>
     if nth 3 ys (x - 1) = 0 then
       (ccDist n (c + 1) (m - k - 1))%xr
     else (ccDist n c (m - k - 1))%xr) <=
     (ccDist n c (m - k))%xr. proof. admitted.


lemma helper3 : forall (n c m k x: int) (ys : int list),
0 < n /\
   n <= m /\
   c = count1 ys /\
   count1 ys + count0 ys = n  /\ 0 <= k /\ isBits ys /\ nth 3 ys (x - 1) = 0   => (ccDist n (count1 (update ys (x - 1) 1))
   (m - (k + 1)))%pos <=
 (ccDist n (c + 1) (m - k - 1))%pos . proof. admitted.

lemma helper4 :  forall (n c m k x: int) (ys : int list),
0 < n /\
   n <= m /\
   c = count1 ys /\
   count1 ys + count0 ys = n  /\ 0 <= k /\ isBits ys /\ nth 3 ys (x - 1) <> 0   => (ccDist n (count1 (update ys (x - 1) 1))
   (m - (k + 1)))%pos <=
 (ccDist n c (m - k - 1))%pos . proof. admitted.

lemma doubleNeg : forall (b :bool), ! (! b) => b. proof. admitted.
    
       
lemma count : forall (l: int list) (j n : int), count1 l + count0 l = n /\ nth 3 l j = 0 =>
    count1 (update l j 1) + count0 (update l j 1) = n. proof. admitted.

lemma count2 : forall (l: int list) (j n : int), count1 l + count0 l = n /\ isBits l =>
    count1 (update l j 1) + count0 (update l j 1) = n. proof. admitted.


lemma isBitsInv : forall (l : int list) (j : int), isBits l => isBits (update l j 1). proof. admitted.


lemma mkZCount : forall (n : int), 0 = count1 (mkzeros n). proof. admitted.
lemma helper5 : forall (n : int), isBits (mkzeros n). proof. admitted.   
lemma mkZCount2 : forall (n : int), count1 (mkzeros n) + count0 (mkzeros n) = n. proof. admitted.
      

op indFnC (k m : int) : real = if k = m then 1.0 else 0.0.



  (*CC distn for parameters n,m is ccDist n 0 m.*)


module CC = {
var n : int
var m : int
var ys : int list
var x : int
var k : int
var c : int  
proc f() : unit = {
  ys <- mkzeros n;
  k <- 0;
  c <- 0;  
  while (hasZero ys)
    {x <$ [1..n];
      ys <- update ys (x - 1) 1;
      c <- count1 ys;
      k <- k + 1;}}}.

ehoare couponC : CC.f : ((0 < CC.n /\ CC.n <= CC.m)  `|` (ccDist CC.n 0 CC.m)%xr) ==> (indFnC CC.k CC.m)%xr.
proof. proc. (*loop invariant is ccDist n c (m - k)*) seq 3: ((0 < CC.n /\ CC.n <= CC.m /\ CC.ys = mkzeros CC.n /\ CC.k = 0 /\ CC.c = 0) `|` (ccDist CC.n 0 CC.m)%xr).  wp. skip. smt.
while ((0 < CC.n /\ CC.n <= CC.m /\ CC.c = count1 CC.ys /\ (count1 CC.ys + count0 CC.ys = CC.n) /\ 0 <= CC.k /\ isBits CC.ys) `|` (ccDist CC.n CC.c (CC.m - CC.k))%xr).  
progress. case (CC.k{hr} = CC.m{hr}). move => H. rewrite H. rewrite/indFnC. simplify. case (hasZero CC.ys{hr} = false). move => H'. rewrite helper.  
smt. case (CC.c{hr} = count1 CC.ys{hr}). move => H''. case (count1 CC.ys{hr} + 0 = CC.n{hr}).   move => H4. case (0 < CC.n{hr}). move => H5. rewrite ccd2. smt. smt. smt. smt. smt. smt. smt. seq 1 :  ((0 < CC.n /\
    CC.n <= CC.m /\ CC.c = count1 CC.ys /\ count1 CC.ys + count0 CC.ys = CC.n /\ 0 <= CC.k /\ isBits CC.ys) `|`
   (if ((nth 3 CC.ys (CC.x - 1)) = 0) then (ccDist CC.n (CC.c + 1) (CC.m - CC.k - 1))%xr else (ccDist CC.n (CC.c) (CC.m - CC.k - 1))%xr)). rnd. skip. progress. case (0 < CC.n{hr} /\
      CC.n{hr} <= CC.m{hr} /\
      CC.c{hr} = count1 CC.ys{hr} /\
      count1 CC.ys{hr} + count0 CC.ys{hr} = CC.n{hr} /\ 0 <= CC.k{hr}). move => H. simplify. case (hasZero CC.ys{hr}). move => H'. case (isBits CC.ys{hr}). simplify. move => H''. rewrite H. simplify.  apply helper2. smt. smt. smt. smt. wp. skip. progress. 
case (nth 3 CC.ys{hr} (CC.x{hr} - 1) = 0). simplify. case (!(0 < CC.n{hr} /\
 CC.n{hr} <= CC.m{hr} /\
 CC.c{hr} = count1 CC.ys{hr} /\
 count1 CC.ys{hr} + count0 CC.ys{hr} = CC.n{hr} /\ 0 <= CC.k{hr} /\ isBits CC.ys{hr})).  smt. move => H. apply doubleNeg in H.  rewrite H. simplify. move => H'. have ->: (0 < CC.n{hr} /\
 CC.n{hr} <= CC.m{hr} /\
 count1 (update CC.ys{hr} (CC.x{hr} - 1) 1) +
 count0 (update CC.ys{hr} (CC.x{hr} - 1) 1) = CC.n{hr} /\ 0 <= CC.k{hr} + 1 /\ isBits (update CC.ys{hr} (CC.x{hr} - 1) 1)). progress.  smt. smt. apply count. smt. smt. apply isBitsInv. smt. simplify. apply helper3. smt. progress. simplify. case (!(0 < CC.n{hr} /\
 CC.n{hr} <= CC.m{hr} /\
 CC.c{hr} = count1 CC.ys{hr} /\
 count1 CC.ys{hr} + count0 CC.ys{hr} = CC.n{hr} /\ 0 <= CC.k{hr} /\ isBits CC.ys{hr})). smt. move => H1. apply doubleNeg in H1. rewrite H1. simplify. have ->: (0 < CC.n{hr} /\
 CC.n{hr} <= CC.m{hr} /\
 count1 (update CC.ys{hr} (CC.x{hr} - 1) 1) +
 count0 (update CC.ys{hr} (CC.x{hr} - 1) 1) = CC.n{hr} /\ 0 <= CC.k{hr} + 1 /\ isBits (update CC.ys{hr} (CC.x{hr} - 1) 1)). progress. smt. smt. apply count2. smt. smt. apply isBitsInv. smt. simplify. apply helper4. smt. skip. progress. case (!(CC.k{hr} = 0)). move => H. smt. move => H. apply doubleNeg in H. case (!(CC.c{hr} = 0)). smt. move => H'. apply doubleNeg in H'. rewrite H. rewrite H'. case (! (0 < CC.n{hr} /\
 CC.n{hr} <= CC.m{hr} /\ CC.ys{hr} = mkzeros CC.n{hr} /\ 0 = 0 /\ 0 = 0)). smt. move => H3. apply doubleNeg in H3. rewrite H3. simplify. have -> : (0 < CC.n{hr} /\
 CC.n{hr} <= CC.m{hr} /\
 0 = count1 CC.ys{hr} /\
 count1 CC.ys{hr} + count0 CC.ys{hr} = CC.n{hr} /\ isBits CC.ys{hr}). progress. smt. smt. have ->: CC.ys{hr} = mkzeros CC.n{hr}. smt.  apply mkZCount. have ->: CC.ys{hr} = mkzeros CC.n{hr}. smt. apply mkZCount2.  have ->: CC.ys{hr} = mkzeros CC.n{hr}. smt. apply helper5. simplify. auto. qed.    

 

