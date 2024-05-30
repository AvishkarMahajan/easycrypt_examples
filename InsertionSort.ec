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

lemma sizePos : forall (l : int list),
    0 < size l + 1.
proof.
admitted.    
    
  







module IsortUC = {
var x : int
var xs : int list
var ys : int list
var i : int
var j : int
var cost : int
proc f() : unit = {
i <- 0;
j <- 1;    
cost <- 0;
ys <- x :: xs;
  while (i < size xs)
    {cost <- cost + 1; i<- i + 1;}
    while ((1 <= j) /\ (j < size ys))
    {i <- 0;
      while (i < size xs) {cost <- cost + 1; i <- i + 1;}
      j <- j + 1;}}}.


module IsortSC = {
var x : int
var xs : int list
var ys : int list
var i : int
var j : int
var cost : int
proc f() : unit = {
i <- 0;
j <- 1;    
cost <- 0;
ys <- x :: xs;
  while (i < size xs)
  {if ((nth 3 xs i) < x) {cost <- cost + 1;}
  else {cost <- cost;}
  i <- i + 1;}  
  while ((1 <= j) /\ (j < size ys))
    {i <- 0;
      while (i < size xs) {cost <- cost; i <- i + 1;}
      j <- j + 1;}}}.
    

lemma isortCost :
equiv [IsortSC.f ~ IsortUC.f : (size IsortSC.xs{1} =  size IsortUC.xs{2}) ==> (IsortSC.cost{1} <= IsortUC.cost{2})]. proc. seq 4 4 : (size IsortSC.xs{1} = size IsortUC.xs{2} /\ size IsortSC.ys{1} = size IsortSC.xs{1} + 1 /\ IsortSC.i{1} = 0 /\ IsortSC.j{1} = 1 /\ IsortSC.cost{1} = 0 /\ IsortUC.i{2} = 0 /\ IsortUC.j{2} = 1 /\ IsortUC.cost{2} = 0 /\ size IsortUC.ys{2} = size IsortUC.xs{2} + 1). wp. skip. smt. seq 1 1 : (size IsortSC.xs{1} = size IsortUC.xs{2} /\ size IsortSC.ys{1} = size IsortSC.xs{1} + 1 /\ IsortSC.j{1} = 1 /\ IsortSC.cost{1} <= IsortUC.cost{2} /\ IsortUC.j{2} = 1 /\ size IsortUC.ys{2} = size IsortUC.xs{2} + 1 /\ IsortSC.i{1} = IsortUC.i{2}). while (size IsortSC.xs{1} = size IsortUC.xs{2} /\ size IsortSC.ys{1} = size IsortSC.xs{1} + 1 /\ IsortSC.j{1} = 1 /\ IsortSC.cost{1} <= IsortUC.cost{2} /\ IsortUC.j{2} = 1 /\ size IsortUC.ys{2} = size IsortUC.xs{2} + 1 /\ IsortSC.i{1} = IsortUC.i{2}). if{1}. wp. skip. smt. wp. skip. smt. skip. smt. while (size IsortSC.xs{1} = size IsortUC.xs{2} /\ size IsortSC.ys{1} = size IsortSC.xs{1} + 1 /\ IsortSC.j{1} = IsortUC.j{2}  /\ IsortSC.cost{1} <= IsortUC.cost{2} /\ size IsortUC.ys{2} = size IsortUC.xs{2} + 1 /\ IsortSC.i{1} = IsortUC.i{2}). seq 1 1 : (size IsortSC.xs{1} = size IsortUC.xs{2} /\ size IsortSC.ys{1} = size IsortSC.xs{1} + 1 /\ IsortSC.j{1} = IsortUC.j{2}  /\ IsortSC.cost{1} <= IsortUC.cost{2} /\ size IsortUC.ys{2} = size IsortUC.xs{2} + 1 /\ IsortSC.i{1} = 0 /\ IsortUC.i{2} = 0). wp. skip. smt. seq 1 1 : ((size IsortSC.xs{1}) = (size IsortUC.xs{2}) /\
  (size IsortSC.ys{1}) = (size IsortSC.xs{1}) + 1 /\
  IsortSC.j{1} = IsortUC.j{2} /\
  IsortSC.cost{1} <= IsortUC.cost{2} /\
  (size IsortUC.ys{2}) = (size IsortUC.xs{2}) + 1 /\
  IsortSC.i{1} = IsortUC.i{2}). while ((size IsortSC.xs{1}) = (size IsortUC.xs{2}) /\
  (size IsortSC.ys{1}) = (size IsortSC.xs{1}) + 1 /\
  IsortSC.j{1} = IsortUC.j{2} /\
  IsortSC.cost{1} <= IsortUC.cost{2} /\
  (size IsortUC.ys{2}) = (size IsortUC.xs{2}) + 1 /\
  IsortSC.i{1} = IsortUC.i{2}). wp. skip. smt. skip. smt. wp. skip. smt. skip. smt. qed.

    
        









        















 


 







        
          
      





  
















 


 







        
          
      





  
