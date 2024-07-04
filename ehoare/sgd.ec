(* Pseudo-code for SGD based on derivation in https://raghumeka.github.io/CS289ML/gdnotes.pdf

x0 : R^d
y : R ^d
v : R^d
y' : R^d
n : pos int
t : pos real
f : R^d -> R
distVec : R^d -> dist (R^d) (distVec takes in a vector x and returns a distribution over vectors such that the expected value of this distribution is grad(f) at x)
i : int
l : R^d list
u : real
x* : real
var : real

i <- 0;
l = [x0];
while (i < n)
{y <- head l;
 v <-$ distVec y;
 y' <- y - t * v;
l <- y' :: l;
i <- i + 1;
 u <- u + f (xi+1)] -(
f (x∗) + 
1/2t (‖xi − x∗‖ − ‖xi+1 − x∗‖) + t*var);} here xi+1 is the head of the list l and xi is the second element of l. x* is the optimizing argument of f.  

given a memory m define g (m) = u 

Then g is a loop invariant => E(g_final) <= g_int (second, third inequality on page 5) 

eHL spec : {u = C /\ var = S | g} P {g} (C is some large positve real, S is also positive)

*)


