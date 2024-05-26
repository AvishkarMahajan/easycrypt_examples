require import List.
require import AllCore.

op size (l : 'a list) : int =
with l = [] => 0
with l = x :: xs => 1 + size xs.

op update (l : 'a list) (pos : int) (k : 'a) : 'a list = 
List.mapi (fun i x => if i = pos then k else x) l.


lemma lem_update2: forall (l : 'a list) (pos pos': int) (k d : 'a),
!(pos = pos')  => nth d (update l pos k) pos' = nth d l pos'.
proof.
  admitted.

lemma lem_update : forall (l : 'a list) (pos : int) (k d : 'a),
nth d (update l pos k) pos = k.
proof.
  admitted.

lemma split_uni_q : forall (p q : int -> bool),
    (forall (n: int), (p n /\ q n)) => (forall (n: int), p n) /\ (forall (n : int), q n).
proof. admitted.


module Compare = {
var i : int
var cost : int  
var xs : int list 
var ys : int list 
var r : bool
proc f() : unit = {
  i <- 0;
  r <- true;
  cost <- 0;
  if (! (size xs = size ys)) {
  r <- false;
  cost <- 1; }
  else {
  while (i < (size xs)) {
  r <- r && (nth 0 xs i = nth 0 ys i);
  i <- i + 1;
  cost <- cost + 1;
      }
    }
  }
}.

lemma lemCompare :
equiv [Compare.f ~ Compare.f : Compare.xs{1} = Compare.xs{2} /\ size (Compare.ys{1}) = size (Compare.ys{2})   ==> ={Compare.cost}].
    proof. proc. seq 3 3 : ( Compare.xs{1} = Compare.xs{2} /\ size (Compare.ys{1}) = size (Compare.ys{2}) /\ Compare.cost{1} = Compare.cost{2} /\ Compare.i{1} = Compare.i{2}). wp. auto. if. progress. rewrite H0. assumption.  rewrite H0. rewrite H. auto. wp. auto. while (={Compare.cost, Compare.xs, Compare.i}). wp. auto. skip. progress. 
  qed.


module Max_elt = {
var result : int
var xs : int list 
var cont_flow : int list
var i : int
proc f() : unit = {
  result <- 0;
  cont_flow <- [];
  i <- 0;  
  while (i < (size xs)) {
  if ((nth 0 xs i) < (nth 0 xs result)) {
  cont_flow <- 0 :: cont_flow;
  i <- i + 1;}
  else { cont_flow <- 1 :: cont_flow;
  result <- i;
  i <- i + 1;}
      
    }
  }
}.


lemma lemMax_elt:
equiv [Max_elt.f ~ Max_elt.f : size (Max_elt.xs{1}) = size (Max_elt.xs{2}) /\ (forall (n m : int), ((n < size (Max_elt.xs{1}) /\ m < size (Max_elt.xs{1})) => ((nth 0 Max_elt.xs{1} n < nth 0 Max_elt.xs{1} m) <=> (nth 0 Max_elt.xs{2} n < nth 0 Max_elt.xs{2} m)))) ==> ={Max_elt.cont_flow}].
    proof. proc. seq 3 3 : (size (Max_elt.xs{1}) = size (Max_elt.xs{2}) /\  (forall (n m : int), ((n < size (Max_elt.xs{1}) /\ m < size (Max_elt.xs{1})) => ((nth 0 Max_elt.xs{1} n < nth 0 Max_elt.xs{1} m) <=> (nth 0 Max_elt.xs{2} n < nth 0 Max_elt.xs{2} m))))  /\ ={Max_elt.cont_flow} /\ ={Max_elt.i} /\ ={Max_elt.result} /\ !(Max_elt.i{1} < Max_elt.result{1}) /\ !(Max_elt.i{2} < Max_elt.result{2})). wp. skip. progress. while ((forall (n m : int), (n < (size Max_elt.xs{1}) /\ m < (size Max_elt.xs{1}) =>
     nth 0 Max_elt.xs{1} n < nth 0 Max_elt.xs{1} m <=>
     nth 0 Max_elt.xs{2} n < nth 0 Max_elt.xs{2} m))/\
      ={Max_elt.cont_flow, Max_elt.i, Max_elt.result} /\!(Max_elt.i{1} < Max_elt.result{1}) /\ size (Max_elt.xs{1}) = size (Max_elt.xs{2})). if. smt. wp. skip. progress. smt. smt. smt.  wp. skip.  smt.  skip. smt.  qed.




module Bin_up = {
var k : int
var xs : int list 
var j : int 
var i : int
var bit_flips : int
proc f() : unit = {
  j <- 0;
  i <- 0;
  bit_flips <- 0;  
  while (i < k) { j <- 0;
      while ((nth 3 xs j) = 1)
      {xs <- update xs j 0;
        bit_flips <- bit_flips + 1;
        j <- j + 1;}
        xs <- update xs j 1;
        i <- i +1;
        bit_flips <- bit_flips + 1;}
  }
}.



module Bin_down = {
var k : int
var xs : int list 
var j : int 
var i : int
var bit_flips : int
proc f() : unit = {
  j <- 0;
  i <- 0;
  bit_flips <- 0;  
  while (i < k) { j <- 0;
      while ((nth 3 xs j) = 0)
      {xs <- update xs j 1;
        bit_flips <- bit_flips + 1;
        j <- j + 1;}
        xs <- update xs j 0;
        i <- i +1;
        bit_flips <- bit_flips + 1;}
  }
}.


lemma binCount:
equiv [Bin_up.f ~ Bin_down.f :  ((forall (n : int),  (nth 3 Bin_up.xs{1} n  = 0)  <=> (nth 3 Bin_down.xs{2} n  = 1)) /\ (forall (n : int), ((nth 3 Bin_up.xs{1} n  = 1)  <=> (nth 3 Bin_down.xs{2} n  = 0))) /\ Bin_up.k{1} = Bin_down.k{2})   ==> (Bin_up.bit_flips{1} = Bin_down.bit_flips{2})].
    proof. proc. seq 3 3 : (((forall (n : int),  (nth 3 Bin_up.xs{1} n  = 0)  <=> (nth 3 Bin_down.xs{2} n  = 1)) /\ (forall (n : int),  ((nth 3 Bin_up.xs{1} n  = 1)  <=> (nth 3 Bin_down.xs{2} n  = 0))) /\ Bin_up.k{1} = Bin_down.k{2} /\ Bin_up.j{1} = Bin_down.j{2} /\ Bin_up.i{1} = Bin_down.i{2} /\ Bin_up.bit_flips{1} = Bin_down.bit_flips{2})). wp. skip. progress. while (((forall (n : int),  (nth 3 Bin_up.xs{1} n  = 0)  <=> (nth 3 Bin_down.xs{2} n  = 1)) /\ (forall (n :int), ((nth 3 Bin_up.xs{1} n  = 1)  <=> (nth 3 Bin_down.xs{2} n  = 0))) /\ Bin_up.k{1} = Bin_down.k{2} /\ Bin_up.j{1} = Bin_down.j{2} /\ Bin_up.i{1} = Bin_down.i{2} /\ Bin_up.bit_flips{1} = Bin_down.bit_flips{2})). seq 1 1 : (((forall (n : int),  (nth 3 Bin_up.xs{1} n  = 0)  <=> (nth 3 Bin_down.xs{2} n  = 1)) /\ (forall (n : int), ((nth 3 Bin_up.xs{1} n  = 1)  <=> (nth 3 Bin_down.xs{2} n  = 0))) /\ Bin_up.k{1} = Bin_down.k{2} /\ Bin_up.j{1} = Bin_down.j{2} /\ Bin_up.i{1} = Bin_down.i{2} /\ Bin_up.bit_flips{1} = Bin_down.bit_flips{2})). wp. skip. progress.  seq 1 1 : (((forall (n : int),  (nth 3 Bin_up.xs{1} n  = 0)  <=> (nth 3 Bin_down.xs{2} n  = 1)) /\ (forall (n : int), ((nth 3 Bin_up.xs{1} n  = 1)  <=> (nth 3 Bin_down.xs{2} n  = 0))) /\ Bin_up.k{1} = Bin_down.k{2} /\ Bin_up.j{1} = Bin_down.j{2} /\ Bin_up.i{1} = Bin_down.i{2} /\ Bin_up.bit_flips{1} = Bin_down.bit_flips{2})).  while (((forall (n : int),  (nth 3 Bin_up.xs{1} n  = 0)  <=> (nth 3 Bin_down.xs{2} n  = 1)) /\(forall (n : int),  ((nth 3 Bin_up.xs{1} n  = 1)  <=> (nth 3 Bin_down.xs{2} n  = 0))) /\ Bin_up.k{1} = Bin_down.k{2} /\ Bin_up.j{1} = Bin_down.j{2} /\ Bin_up.i{1} = Bin_down.i{2} /\ Bin_up.bit_flips{1} = Bin_down.bit_flips{2})). wp. skip. progress. auto. case (Bin_down.j{2} = n).  move => H'. rewrite H'. smt. move => H'.  rewrite lem_update2.  auto.  move: H'=> H6. move : H2 => H2. move : H3 => H3.
rewrite  lem_update2 in H3. auto.  smt.  smt.  smt.  smt. smt. smt. skip. progress. smt. 
      smt. wp. skip. progress. smt. smt. case (Bin_down.j{2} = n). move => H'. rewrite H'. rewrite lem_update. auto. move => H'.  rewrite lem_update2. auto.  move : H1 => H1. rewrite lem_update2 in H1. auto. smt. smt. skip. smt. qed.


module Len = {
var k : int
var j : int
var xs : int list
var ys : int list
var cost : int 
proc f() : unit = {
k <- 0;
cost <- 0;
ys <- [];
j <- 0;    
while (k < size xs)
{ ys <- 1 :: ys;
  cost <- cost + 1;
  k <- k + 1;}
while (j < size ys)
{cost <- cost + 1;
  j <- j + 1;}
}
}.

module Len_tailRec = {
var k : int
var j : int
var xs : int list
var ys : int list
var cost : int 
proc f() : unit = {
k <- 0;
cost <- 0;
ys <- [];
j <- 0;    
while (k < size xs)
{ ys <- 1 :: ys;
  cost <- cost + 1;
  k <- k + 1;}
while (j < size ys)
{cost <- cost + 0;
  j <- j + 1;}
}
}.



lemma lencost :
equiv [Len.f ~ Len_tailRec.f : (size Len.xs{1} = size Len_tailRec.xs{2}) ==> !(Len.cost{1} < Len_tailRec.cost{2})].
proof. proc. seq  4 4 : (size Len.xs{1} = size Len_tailRec.xs{2} /\ Len.cost{1} = Len_tailRec.cost{2} /\ Len.k{1} = Len_tailRec.k{2} /\ Len.ys{1} = Len_tailRec.ys{2} /\ Len.j{1} = Len_tailRec.j{2}). wp. skip. smt. seq 1 1 : (size Len.xs{1} = size Len_tailRec.xs{2} /\ Len.cost{1} = Len_tailRec.cost{2} /\ Len.k{1} = Len_tailRec.k{2} /\ Len.ys{1} = Len_tailRec.ys{2} /\ Len.j{1} = Len_tailRec.j{2}). while (size Len.xs{1} = size Len_tailRec.xs{2} /\ Len.cost{1} = Len_tailRec.cost{2} /\ Len.k{1} = Len_tailRec.k{2} /\ Len.ys{1} = Len_tailRec.ys{2} /\ Len.j{1} = Len_tailRec.j{2}). wp. skip. smt. skip. smt. while (size Len.xs{1} = size Len_tailRec.xs{2} /\(! (Len.cost{1} < Len_tailRec.cost{2})) /\ Len.k{1} = Len_tailRec.k{2} /\ Len.ys{1} = Len_tailRec.ys{2} /\ Len.j{1} = Len_tailRec.j{2}). wp. skip. smt. skip. smt. qed. 



module Find1 = {
var k : int
var i : int
var xs : int list
var b : bool  
var cost : int 
proc f() : unit = {
i <- 0;
cost <- 0;
b <- false;    
  while ((i < size xs) /\ (b = false))
    { if ((nth 3 xs i) = k)
      {b <- true;
        cost <- cost + 1;
        i <- i + 1;}
        else {
        cost <- cost + 1;
        i <- i + 1;}}}
  }.
        


module Find2 = {
var k : int
var i : int
var xs : int list
var b : bool  
var cost : int 
proc f() : unit = {
i <- 0;
cost <- size xs - 1;
b <- false;    
  while ((i < size xs) /\ (b = false))
    { if ((nth 3 xs (size xs - i - 1)) = k)
      {b <- true;
        cost <- cost + 1;
        i <- i + 1;}
        else {
        cost <- cost + 1;
        i <- i + 1;}}}
}.


lemma findCost :
equiv [Find1.f ~ Find2.f : (size Find1.xs{1} = size Find2.xs{2}) /\ (0 < size Find1.xs{1}) ==> !(Find2.cost{2} < Find1.cost{1})]. proc. seq 3 3 : ((size Find1.xs{1} = size Find2.xs{2}) /\ (0 < size Find1.xs{1}) /\ Find1.i{1} = 0 /\ Find2.i{2} = 0 /\ ((size Find2.xs{2} -1) = Find2.cost{2}) /\ Find1.cost{1} = 0 /\ Find1.b{1} = false /\ Find2.b{2} = false). wp. skip. smt. unroll{1} 1. unroll{2} 1. seq 1 1 : ((size Find1.xs{1} = size Find2.xs{2}) /\ (0 < size Find1.xs{1}) /\ Find1.i{1} = 1 /\ Find2.i{2} = 1 /\ Find1.cost{1} = 1 /\  Find2.cost{2} = size Find1.xs{1}). if. smt. if{1}. if{2}. wp. skip. smt.  wp. skip. smt. if{2}. wp. skip. smt. wp. skip. smt. skip. smt. while{1} ((Find1.i{1} = Find1.cost{1})/\ !(size Find1.xs{1} < Find1.i{1})) (size Find1.xs{1} - Find1.i{1}). progress. if. wp. skip. smt. wp. skip. smt. progress.  while{2} (forall (j : int), Find2.k{2} = j => !(Find2.cost{2} < size Find2.xs{2})) (size Find2.xs{2} - Find2.i{2}). progress. if. wp. skip. progress.  smt. smt. wp.   skip.  smt. skip.  smt.  qed. 




        















 


 







        
          
      





  
















 


 







        
          
      





  
