require import AllCore List Xreal Distr RealSeries DInterval Finite.
require import StdRing StdBigop DBool.

import Bigreal Rpbar.RealNotation.

hint simplify BRA.big_nil, BRA.big_cons.
hint simplify range_ltn, range_geq.

lemma predTE ['a] (x : 'a) : predT x = true.
proof. by done. qed.

hint simplify predTE.

lemma L : E [0..1] (fun x => if x = 1 then 1.0 else 0.0) = 0.5.
proof.
rewrite fin_expE /=.
- by exists [0; 1]; split=> //; smt(supp_dinter).
have := perm_eq_dinter 0 1 => /BRA.eq_big_perm -> /=.
by rewrite dinter1E.
qed.

lemma L' : forall (g : int -> real), E [0..1] (fun x => g x) = 0.5* (g 0 + g 1).
proof. progress.
rewrite fin_expE /=.
- by exists [0; 1]; split=> //; smt(supp_dinter).
have := perm_eq_dinter 0 1 => /BRA.eq_big_perm -> /=.
rewrite dinter1E. simplify. smt.
qed.

lemma L2 : Ep [0..1] (fun x => if x = 1 then 1.0%xr else 0.0%xr) = 0.5%xr.
proof.
rewrite EP_E/is_real /to_real.
- by move=> x /=; case: (x = 1) => /=.
- by apply: (summable_fin _ [0; 1])=> x /=; case: (x = 1).
pose f (x : int) := to_real (if x = 1 then 1.0%xr else 0.0%xr).
have ->: f = (fun x => if x = 1 then 1.0 else 0.0).
- by apply/fun_ext=> x @/f /=; case (x = 1).
by rewrite L.
qed.



lemma L3 : forall (g : int -> real), Ep [0..1] (fun x => ((g x)%xr)) = 0.5%xr * ((g 0)%xr + (g 1)%xr).
proof. progress. rewrite EP_E/is_real /to_real.
- by move=> x /=; case: (x = 1) => /=.
- apply: (summable_fin _ [0; 1])=> x /=; case: (x = 1). progress.
simplify. 
case (x = 0). simplify. auto. smt. rewrite L'. smt. qed.

lemma Lb : forall (g : bool -> real), E {0,1} (fun x => g x) = 0.5* (g false + g true).
proof.  progress.
rewrite fin_expE /=.
- by exists [false; true]; split=> //; smt(supp_dbool). search to_seq. admitted.
(*have := perm_eq_d [0 1] => /BRA.eq_big_perm -> /=.
rewrite dinter1E. simplify. smt.
  qed.*)

lemma L4 : forall (g : bool -> real), Ep {0,1} (fun x => ((g x)%xr)) = 0.5%xr * ((g false)%xr + (g true)%xr).
proof. progress. rewrite EP_E/is_real /to_real.
- by move=> x /=; case: (x = true) => /=.
search summable. - apply: (summable_fin _ [false; true])=> x /=; case: (x = true). progress.
simplify. 
  case (x = false). simplify. auto. smt. rewrite Lb. smt. qed.

lemma divBy2: forall (x y : real), (0.0 <= x /\ 0.0 <= y) => inv 2%rp * (x%rp + y%rp)  = (x /2%r + y /2%r)%rp. proof. move => x. move => y. smt. qed.





