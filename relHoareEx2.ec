(* Length of list, Find elt in list*)
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




        















 


 







        
          
      





  
















 


 







        
          
      





  
