require import List.
require import AllCore.

op size (l : 'a list) : int =
with l = [] => 0
with l = x :: xs => 1 + size xs.

op count1 (l : int list) : int =
with l = [] => 0
with l = x :: xs => if x = 1 then (1 + count1 xs) else count1 xs.

op head' (l : int list) : int =
with l = [] => 3
with l = x :: xs => x.

op tail' (l : int list) : int list =
with l = [] => []
with l = x :: xs => xs.



op take (i : int) (l : int list) : int list = if i = 0 then l else (if l = [] then [] else head' l :: take (i-1) (tail' l)).




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

lemma count : forall (l : int list) (i : int),
(i < size l) /\ (nth 3 l i) = 1 => count1 (take i l) + 1 = count1 (take (i + 1) l).
proof.
  admitted.

lemma count2 : forall (l : int list) (i : int),
(i < size l) /\ (nth 3 l i) <> 1 => count1 (take i l) = count1 (take (i + 1) l).
proof.
  admitted.

lemma countEmpty : forall (l : int list),
0 = count1 (take 0 l).
proof.
  admitted.

lemma count3 : forall (i j : int) (l l' : int list),
    (! i < size l) /\ (! j < size l') => count1 (take i l) - count1 (take j l') = count1 l - count1 l'.
proof.
admitted.    
    
  





module SamCost = {
var i : int
var xs : int list
var cost : int 
proc f() : unit = {
i <- 0;
cost <- 0;
 while (i < size xs) 
    { if ((nth 3 xs i) = 1)
      {i <- i + 1;
        cost <- cost + 1;}
        else {
        
        i <- i + 1;}}}
}.


lemma samCostDiff :
equiv [SamCost.f ~ SamCost.f : (count1 SamCost.xs{1} <=  count1 SamCost.xs{2}) ==> ((SamCost.cost{2} - SamCost.cost{1}) = (count1 SamCost.xs{2} - count1 SamCost.xs{1}))]. proc.  seq 2 2 : ((count1 SamCost.xs{1} <=  count1 SamCost.xs{2}) /\ SamCost.cost{1} = 0 /\ SamCost.cost{2} = 0 /\ SamCost.i{1} = 0 /\ SamCost.i{2} = 0). wp. skip. smt. while{1} (SamCost.cost{1} = count1 (take SamCost.i{1} SamCost.xs{1}) ) (size SamCost.xs {1} - SamCost.i{1}). progress. if. wp. skip. progress. apply count. smt. smt. wp. skip. progress. apply count2. smt. smt.  while{2} (SamCost.cost{2} = count1 (take SamCost.i{2} SamCost.xs{2}) ) (size SamCost.xs {2} - SamCost.i{2}). progress. if. wp. skip. progress. apply count. smt. smt. wp. skip. progress. apply count2. smt. smt. skip. progress. apply countEmpty.  smt.  apply countEmpty. smt. apply count3. smt. qed.
(* from this it follows that the cost differece is at most the number of list entries that differ since this number is greater than or equal to the difference in the number of 1s*)






        















 


 







        
          
      





  
















 


 







        
          
      





  
