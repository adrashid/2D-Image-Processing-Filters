(* ========================================================================= *)
(*                                                                           *)
(*             Formal Analysis of 2D Image Processing Filters                *)
(*                                                                           *)
(*    (c) Copyright, Adnan Rashid*, Sa'ed Abed** and Osman Hasan*            *)
(*       *System Analysis and Verification (SAVe) Lab,                       *)
(*        National University of Sciences and Technology (NUST), Pakistan    *)
(*                                                                           *)
(*       **Computer Engineering Department,                                  *)
(*         College of Engineering and Petroleum, Kuwait University, Kuwait   *)
(*                                                                           *)
(* ========================================================================= *)

let z_transform_2d  = new_definition `
    z_transform_2d (f:num->num->complex) (z1:complex) z2 = 
    infsum (from 0) (\n1. infsum (from 0) (\n2. f n1 n2 / (z1 pow n1 * z2 pow n2)))`;;    

let Z_TRANSFORM_2D = prove (`
  !f z. z_transform_2d f z1 z2 = 
      infsum (from 0) (\n1. infsum (from 0) (\n2. f n1 n2 * inv z1 pow n1 * inv z2 pow n2))`,
 SIMP_TAC[complex_div; z_transform_2d; COMPLEX_INV_MUL; GSYM COMPLEX_POW_INV]);;

let z_tr_summable =  new_definition `
    z_tr_summable (f:num->num->complex) (z1:complex) z2 (n1:num) <=> 
     (!n1. summable (from 0) (\n2. f n1 n2 / (z1 pow n1 * z2 pow n2)))`;;

let z_tr_td_summable =  new_definition `
    z_tr_td_summable (f:num->num->complex) (z1:complex) z2 <=> 
           (?l. ((\n1. infsum (from 0) 
              (\n2. f n1 n2 * inv z1 pow n1 * inv z2 pow n2)) 
                           sums l) (from 0))`;;

let roc_2d = new_definition `
       roc_2d (f:num->num->complex) (n1:num) = 
         {(z1, z2) | ~(z1 = Cx(&0)) /\ ~(z2 = Cx(&0)) /\ z_tr_summable f z1 z2 n1 /\ z_tr_td_summable f z1 z2}`;;

let INFSUM_LIM = prove (`
     !s f. infsum s f = lim sequentially (\k. vsum (s INTER (0..k)) f)`,
         REWRITE_TAC [infsum; sums; GSYM lim]);;

let CPOW_POW = prove (
   ` !n w. ~(w = Cx(&0)) ==> w cpow Cx(&n) = w pow n`,
INDUCT_TAC THENL[
GEN_TAC THEN 
SIMP_TAC[cpow;complex_pow;COMPLEX_MUL_LZERO;CEXP_0];
SIMP_TAC[cpow;complex_pow;COMPLEX_MUL_LZERO;CEXP_0; ADD1;
       CX_ADD;GSYM REAL_OF_NUM_ADD;COMPLEX_ADD_RDISTRIB;
      COMPLEX_MUL_LID;GSYM CEXP_ADD] THEN 
REWRITE_TAC[MESON[GSYM CEXP_ADD]`cexp ((Cx (&n) * clog w) + clog w) 
            = cexp (Cx (&n) * clog w)* cexp(clog w)`] THEN
SIMP_TAC[CEXP_CLOG; 
           COMPLEX_FIELD `w * w pow n =  (w pow n) * w`] THEN 
SIMP_TAC[COMPLEX_EQ_MUL_RCANCEL] THEN 
POP_ASSUM MP_TAC THEN 
SIMP_TAC[cpow]]);;


let ROC_2D_NOT_ZERO = prove(
  `!f z1 z2 (n1:num). (z1, z2) IN roc_2d f n1 ==> ~(z1 = Cx(&0)) /\ ~(z2 = Cx(&0))`,
     SIMP_TAC[roc_2d; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     ASM_MESON_TAC [PAIR_EQ]);;

(*===================================================================*)
(*   Here we define variant of 2D z-transform using "cpow" and then  *)
(*   we will prove the equivalence. 	   	 	    	     *)
(*   NOTE: This is quite handy to prove further properties becasue   *)
(*   considerig z^(n:num) is sometime difficult than z^(Cx(&n))      *)
(*===================================================================*)

let z_tr_2d  = new_definition `
    z_tr_2d (f:num->num->complex) (z1:complex) z2 = 
    infsum (from 0) (\n1. infsum (from 0) 
             (\n2. f n1 n2 * z1 cpow --Cx(&n1) * z2 cpow --Cx(&n2)))`;;

let z_tr_summable_cpow =  new_definition `
    z_tr_summable_cpow (f:num->num->complex) (z1:complex) z2 (n1:num) <=> 
       (!n1. summable (from 0) (\n2. f n1 n2 * z1 cpow --Cx(&n1) * z2 cpow --Cx(&n2)))`;;

let z_tr_2d_summable_cpow =  new_definition `
    z_tr_2d_summable_cpow (f:num->num->complex) (z1:complex) z2 <=> 
           (?l. ((\n1. infsum (from 0) 
                (\n2. f n1 n2 * z1 cpow --Cx(&n1) * z2 cpow --Cx(&n2))) 
                           sums l) (from 0))`;;

let ROC_2d = new_definition `
          ROC_2d (f:num->num->complex) (n1:num) = 
             {(z1, z2) | z_tr_summable_cpow f z1 z2 n1 /\ z_tr_2d_summable_cpow f z1 z2}`;;

let ROC_Z_2D_SUMMABLE_CPOW = prove (` 
    !f z1 z2 n1. (z1, z2) IN ROC_2d f (n1:num) <=> 
        z_tr_summable_cpow f z1 z2 n1 /\ z_tr_2d_summable_cpow f z1 z2`,
       REWRITE_TAC [IN; ROC_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
       ASM_MESON_TAC [PAIR_EQ]);;

(*----------------------------------------------*)

let INFSUM_COMPLEX_LMUL = prove
  (`!c f s.  summable  s f ==> 
    infsum s (\n. c * (f n))  = c * infsum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE 
   THEN ASM_SIMP_TAC[GSYM SERIES_COMPLEX_LMUL;SUMS_INFSUM]);;
 
g `!s x (c:complex). summable s x
          ==> infsum s (\n. c * x n) = c * infsum s x`;;

e (REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
     MATCH_MP_TAC SERIES_COMPLEX_LMUL);;
e (ASM_REWRITE_TAC[SUMS_INFSUM]);;

let INFSUM_COMPLEX_LMUL_GEN = top_thm();;

g `!(f:num->num->complex) z1 z2 (a:complex) (n1:num). 
    (z1, z2) IN ROC_2d f n1
        ==> (z1, z2) IN ROC_2d (\n1 n2. a * f n1 n2) n1`;;

e (REWRITE_TAC[IN; ROC_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow; IN_ELIM_THM]);;
e (REPEAT STRIP_TAC);;
e (EXISTS_TAC `z1':complex`);;
e (EXISTS_TAC `z2':complex`);;
e (REPEAT STRIP_TAC);;
e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;
e (ASM_SIMP_TAC [SUMMABLE_COMPLEX_LMUL]);;
e (SUBGOAL_THEN `!n1. infsum (from 0) (\n2. a * (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) n2) = a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))` ASSUME_TAC);;
      e (GEN_TAC);;
      e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
      e (POP_ASSUM MP_TAC THEN SIMP_TAC [PAIR_EQ]);;
      e (ASM_SIMP_TAC []);;
      e (ONCE_REWRITE_TAC [GSYM COMPLEX_MUL_ASSOC]);;

e (POP_ASSUM MP_TAC);;
e (POP_ASSUM MP_TAC THEN SIMP_TAC [PAIR_EQ]);;
e (SIMP_TAC []);;
e (REPEAT DISCH_TAC);; 
e (POP_ASSUM (K ALL_TAC));;
e (EXISTS_TAC `(a:complex) * l`);;
e (ASM_SIMP_TAC [SERIES_COMPLEX_LMUL]);;
e (ASM_SIMP_TAC []);;

let ROC_2D_COMPLEX_LMUL_CPOW = top_thm();;

let ROC_SIMP_TAC = REPEAT (ASM_SIMP_TAC [ROC_2D_COMPLEX_LMUL_CPOW]);;

g `!(f:num->num->complex) z1 z2 (a:complex) b g (n1:num). 
    (z1, z2) IN ROC_2d f n1 /\ 
    (z1, z2) IN ROC_2d g n1
       ==> (z1, z2) IN ROC_2d (\n1 n2. a * f n1 n2) n1 INTER ROC_2d (\n1 n2. b * g n1 n2) n1`;;

e (SIMP_TAC[INTER; IN_ELIM_THM]);;
e (REPEAT GEN_TAC);;
e (ROC_SIMP_TAC);;

let ROC_2D_LINEAR = top_thm ();;

g `!z1 z2 a f n1. (z1, z2) IN ROC_2d f (n1:num) ==> (z1, z2) IN ROC_2d (\n1 n2. f n1 n2 / a) n1`;;

e (REWRITE_TAC [complex_div]);;
e (ONCE_REWRITE_TAC [COMPLEX_MUL_SYM]);;
e (REPEAT STRIP_TAC);;
e (ROC_SIMP_TAC);;

let ROC_2D_SCALING = top_thm ();;

let INFSUM_REINDEX = prove
   (`!f n k.  summable  (from n) (\x. f (x + k)) ==>
       infsum  (from (n+k)) f = infsum  (from n) (\x. f(x+k)) `,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE 
   THEN ASM_SIMP_TAC[GSYM SUMS_REINDEX;SUMS_INFSUM]);;

let SUMMABLE_OFFSET = prove 
 (`!f s n m. summable (from m)  f  /\  0 < n/\ m <= n ==> 
    summable (from n)  f`, MESON_TAC[LE_LT;summable;SUMS_OFFSET]);;

let SPEC_V (x,v) thm = (SPEC v o GEN x  o SPEC_ALL) thm;;

let   INFSUM_REINDEX_0 = prove
   (`!f k.  0 < k /\ summable  (from 0) f ==>
       infsum  (from k) f = infsum  (from 0) (\x. f(x+k)) `,
    MESON_TAC[REWRITE_RULE [ADD] (SPEC_V (`n:num`,`0`) INFSUM_REINDEX);
	SUMMABLE_REINDEX;ADD;LE_0;SUMMABLE_OFFSET]);;
		
let SUMMABLE_COMPLEX_LMUL = prove
  (`!c f s.  summable s f ==> summable s (\n. c * (f n)) `, 
   MESON_TAC[summable;SERIES_COMPLEX_LMUL]);;
   
let INFSUM_COMPLEX_LMUL = prove
  (`!c f s.  summable  s f ==> 
    infsum s (\n. c*(f n))  = c * infsum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE 
   THEN ASM_SIMP_TAC[GSYM SERIES_COMPLEX_LMUL;SUMS_INFSUM]);;
 
let INFSUM_OFFSET = prove
(`!f n m. summable  (from m) f 
   /\ 0 < n /\ m <= n ==> 
 infsum (from m)  f =
   vsum (m..n-1) f + infsum  (from n) f`,
 REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUMS_INFSUM] THEN
 DISCH_THEN(MP_TAC o MATCH_MP SUMS_OFFSET) THEN 
 MESON_TAC[VECTOR_ARITH `(x:complex) = y + z <=> z = x - y`;INFSUM_UNIQUE]);;

g ` !(f:num->num->complex)  (g:num->num->complex) (z1:complex) z2 (n1:num). 
     z_tr_summable_cpow f z1 z2 n1 /\ 
     z_tr_2d_summable_cpow f z1 z2 /\ 
     z_tr_summable_cpow g z1 z2 n1 /\
     z_tr_2d_summable_cpow g z1 z2 ==>
           (z_tr_2d ((\n1 n2. f n1 n2 + g n1 n2)) z1 z2 = z_tr_2d f z1 z2 +  z_tr_2d g z1 z2)`;;

e (REWRITE_TAC[z_tr_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [COMPLEX_ADD_RDISTRIB]);;

e (SUBGOAL_THEN `!n1. (infsum (from 0)
      (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2) +
           g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) =
       (infsum (from 0)
      (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) + 
     (infsum (from 0)
      (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))
      ` ASSUME_TAC);;
      e (GEN_TAC);;
      e (MATCH_MP_TAC INFSUM_ADD);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC INFSUM_ADD);;
e (REWRITE_TAC [summable]);;
e (STRIP_TAC);;
e (EXISTS_TAC `l:complex`);;
e (ASM_SIMP_TAC []);;
e (EXISTS_TAC `l':complex`);;
e (ASM_SIMP_TAC []);;

let ZTR_2D_ADD = top_thm ();;

g ` !(f:num->num->complex)  (g:num->num->complex) (z1:complex) z2 (n1:num). 
     z_tr_summable_cpow f z1 z2 n1 /\ 
     z_tr_2d_summable_cpow f z1 z2 /\ 
     z_tr_summable_cpow g z1 z2 n1 /\
     z_tr_2d_summable_cpow g z1 z2 ==>
           (z_tr_2d ((\n1 n2. f n1 n2 - g n1 n2)) z1 z2 = z_tr_2d f z1 z2 - z_tr_2d g z1 z2)`;;

e (REWRITE_TAC[z_tr_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [COMPLEX_SUB_RDISTRIB]);;

e (SUBGOAL_THEN `!n1. (infsum (from 0)
      (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2) -
           g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) =
       (infsum (from 0)
      (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) - 
     (infsum (from 0)
      (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))
      ` ASSUME_TAC);;
      e (GEN_TAC);;
      e (MATCH_MP_TAC INFSUM_SUB);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC []);;
e (MATCH_MP_TAC INFSUM_SUB);;
e (REWRITE_TAC [summable]);;
e (STRIP_TAC);;
e (EXISTS_TAC `l:complex`);;
e (ASM_SIMP_TAC []);;
e (EXISTS_TAC `l':complex`);;
e (ASM_SIMP_TAC []);;

let ZTR_2D_SUB = top_thm ();;

g ` !c (f:num->num->complex) (z1:complex) z2 (n1:num). 
     z_tr_summable_cpow f z1 z2 n1 /\ 
     z_tr_2d_summable_cpow f z1 z2  ==>
           (z_tr_2d (\n1 n2. c * f n1 n2) z1 z2 = c * z_tr_2d (\n1 n2. f n1 n2) z1 z2)`;;

e (REWRITE_TAC[z_tr_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow]);;
e (REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC]);;
e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. c * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = (c * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (GEN_TAC);;
      e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
e (REWRITE_TAC [summable]);;
e (EXISTS_TAC `l:complex`);;
e (ASM_SIMP_TAC []);;

let ZTR_2D_CONST_MUL = top_thm ();;

g ` !(f:num->num->complex) (g:num->num->complex) (z1:complex) z2 a b (n1:num). 
     z_tr_summable_cpow f z1 z2 n1 /\ 
     z_tr_2d_summable_cpow f z1 z2 /\ 
     z_tr_summable_cpow g z1 z2 n1 /\
     z_tr_2d_summable_cpow g z1 z2 ==>
           (z_tr_2d ((\n1 n2. a * f n1 n2 + b * g n1 n2)) z1 z2 = 
              a * z_tr_2d f z1 z2 +  b * z_tr_2d g z1 z2)`;;

e (REWRITE_TAC [z_tr_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow]);;
e (REWRITE_TAC [COMPLEX_ADD_RDISTRIB; GSYM COMPLEX_MUL_ASSOC]);;
e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `!n1. (infsum (from 0)
      (\n2. (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) n2 +
           (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) n2)) = 
      (infsum (from 0)
      (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) +
    (infsum (from 0)
      (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (GEN_TAC);;
      e (MATCH_MP_TAC INFSUM_ADD);;
      e (CONJ_TAC);;
      e (ASM_SIMP_TAC [SUMMABLE_COMPLEX_LMUL]);;
      e (ASM_SIMP_TAC [SUMMABLE_COMPLEX_LMUL]);;

e (POP_ASSUM MP_TAC);;
e (SIMP_TAC []);;
e (DISCH_TAC THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `infsum (from 0)
 (\n1. infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) +
      infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
  infsum (from 0)
 (\n1. infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) +
  infsum (from 0)
 (\n1. infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))
  ` ASSUME_TAC);;
      e (MATCH_MP_TAC INFSUM_ADD);;
      e (CONJ_TAC);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `a * l:complex`);;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;
      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (ASM_SIMP_TAC [SERIES_COMPLEX_LMUL]);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `b * l':complex`);;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (b * infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;
      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (ASM_SIMP_TAC [SERIES_COMPLEX_LMUL]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;
 
      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (b * infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `infsum (from 0)
 (\n1. a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
   a *
 infsum (from 0)
 (\n1. infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `l:complex`);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (AP_TERM_TAC);;
e (SUBGOAL_THEN `infsum (from 0)
 (\n1. b * infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
   b *
 infsum (from 0)
 (\n1. infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `l':complex`);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC []);;

let ZTR_2D_ADD_LINEAR_ALT = top_thm ();;

(*================================================================================*)

g `!(f:num->num->complex)  (g:num->num->complex) (z1:complex) z2 a b (n1:num). 
 (z1, z2) IN ROC_2d f n1 INTER ROC_2d g n1  ==>
           (z_tr_2d (\n1 n2. a * f n1 n2 + b * g n1 n2) z1 z2 =
             a * z_tr_2d f z1 z2 + b * z_tr_2d g z1 z2)`;;

e (SIMP_TAC [INTER; IN_ELIM_THM; ROC_Z_2D_SUMMABLE_CPOW]);;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC ZTR_2D_LINEAR_ALT);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

let ZTR_2D_ADD_LINEAR = top_thm ();;

g ` !(f:num->num->complex) (g:num->num->complex) (z1:complex) z2 a b (n1:num). 
     z_tr_summable_cpow f z1 z2 n1 /\ 
     z_tr_2d_summable_cpow f z1 z2 /\ 
     z_tr_summable_cpow g z1 z2 n1 /\
     z_tr_2d_summable_cpow g z1 z2 ==>
           (z_tr_2d ((\n1 n2. a * f n1 n2 - b * g n1 n2)) z1 z2 = 
              a * z_tr_2d f z1 z2 -  b * z_tr_2d g z1 z2)`;;

e (REWRITE_TAC [z_tr_2d; z_tr_summable_cpow; z_tr_2d_summable_cpow]);;
e (REWRITE_TAC [COMPLEX_SUB_RDISTRIB; GSYM COMPLEX_MUL_ASSOC]);;
e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `!n1. (infsum (from 0)
      (\n2. (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) n2 -
           (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) n2)) = 
      (infsum (from 0)
      (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) -
    (infsum (from 0)
      (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (GEN_TAC);;
      e (MATCH_MP_TAC INFSUM_SUB);;
      e (CONJ_TAC);;
      e (ASM_SIMP_TAC [SUMMABLE_COMPLEX_LMUL]);;
      e (ASM_SIMP_TAC [SUMMABLE_COMPLEX_LMUL]);;

e (POP_ASSUM MP_TAC);;
e (SIMP_TAC []);;
e (DISCH_TAC THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `infsum (from 0)
 (\n1. infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) -
      infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
  infsum (from 0)
 (\n1. infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) -
  infsum (from 0)
 (\n1. infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))
  ` ASSUME_TAC);;
      e (MATCH_MP_TAC INFSUM_SUB);;
      e (CONJ_TAC);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `a * l:complex`);;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;
      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (ASM_SIMP_TAC [SERIES_COMPLEX_LMUL]);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `b * l':complex`);;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (b * infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;
      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (ASM_SIMP_TAC [SERIES_COMPLEX_LMUL]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. a * f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;
 
      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (SUBGOAL_THEN `!n1. (infsum (from 0) (\n2. b * g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
         (b * infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
            e (GEN_TAC);;
      	    e (ASM_SIMP_TAC [INFSUM_COMPLEX_LMUL]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `infsum (from 0)
 (\n1. a * infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
   a *
 infsum (from 0)
 (\n1. infsum (from 0) (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `l:complex`);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (AP_TERM_TAC);;
e (SUBGOAL_THEN `infsum (from 0)
 (\n1. b * infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) = 
   b *
 infsum (from 0)
 (\n1. infsum (from 0) (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (MATCH_MP_TAC INFSUM_COMPLEX_LMUL);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `l':complex`);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC []);;

let ZTR_2D_SUB_LINEAR_ALT = top_thm ();;

(*========================================================*)

g `!(f:num->num->complex)  (g:num->num->complex) (z1:complex) z2 a b (n1:num). 
 (z1, z2) IN ROC_2d f n1 INTER ROC_2d g n1  ==>
           (z_tr_2d (\n1 n2. a * f n1 n2 - b * g n1 n2) z1 z2 =
             a * z_tr_2d f z1 z2 - b * z_tr_2d g z1 z2)`;;

e (SIMP_TAC [INTER; IN_ELIM_THM; ROC_Z_2D_SUMMABLE_CPOW]);;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC ZTR_2D_SUB_LINEAR_ALT);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

let ZTR_2D_SUB_LINEAR = top_thm ();;


let INV_CPOW = prove (
   `!n z. ~(z = Cx(&0)) ==>  z cpow --Cx(&n) = (inv z) cpow Cx(&n)`,  

INDUCT_TAC THENL[
REWRITE_TAC[CPOW_NEG] THEN 
SIMP_TAC[cpow; COMPLEX_FIELD ` !z. 
                     ~(z = Cx (&0)) ==> ~(inv z = Cx (&0))`] THEN 
SIMP_TAC[COMPLEX_MUL_LZERO;CEXP_0] THEN 
CONV_TAC COMPLEX_FIELD;

REWRITE_TAC[ADD1;GSYM REAL_OF_NUM_ADD;CX_ADD] THEN 
SIMP_TAC[COMPLEX_FIELD 
         `--(Cx (&n) + Cx (&1))= (--Cx (&n) + --Cx (&1)) `;
         GSYM CX_NEG; CPOW_ADD] THEN 
REWRITE_TAC[CX_NEG] THEN 
ASM_SIMP_TAC[] THEN 
SIMP_TAC[COMPLEX_EQ_MUL_LCANCEL] THEN 
REPEAT STRIP_TAC THEN 
DISJ2_TAC THEN
ASM_SIMP_TAC[cpow; COMPLEX_FIELD ` !z. 
                     ~(z = Cx (&0)) ==> ~(inv z = Cx (&0))`] THEN 
SIMP_TAC[COMPLEX_MUL_LID; 
        COMPLEX_FIELD `--Cx (&1) * clog z= --(Cx (&1) * clog z)`] THEN 
ASM_SIMP_TAC[CEXP_CLOG;CEXP_NEG; COMPLEX_FIELD ` !z. 
                     ~(z = Cx (&0)) ==> ~(inv z = Cx (&0))`]]);;

let CPOW_INV = prove ( ` 
      !a k. (Im a = &0 ==> &0 < Re a) ==> a cpow k = inv a cpow --k`,

REPEAT GEN_TAC THEN ASM_CASES_TAC `a = Cx(&0)` THEN 
ASM_SIMP_TAC[cpow;COMPLEX_MUL_RZERO;COMPLEX_INV_0] THEN 
ASM_SIMP_TAC[cpow;COMPLEX_MUL_RZERO;COMPLEX_INV_0; 
COMPLEX_FIELD ` ~(a = Cx(&0)) ==> ~(inv a = Cx(&0))`;
COMPLEX_FIELD ` --a*b = --(a*b)`;CLOG_INV;
COMPLEX_FIELD `--(k * --clog a) = k * clog a`]);;

(*--------------------------------------------------------------*)

g ` !f z1 z2 h1 h2. 
     z_tr_2d (\n1 n2. h1 cpow Cx(&n1) * h2 cpow Cx(&n2) * f n1 n2) z1 z2 = 
    (z_tr_2d (\n1 n2. f n1 n2) (inv h1 * z1) (inv h2 * z2))`;;

e (REPEAT GEN_TAC);;
e (ASM_CASES_TAC `z1 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]);;
e (ASM_CASES_TAC `z2 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]);;

e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]);;
e (ASM_CASES_TAC `h1 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_INV_0]);;
e (ASM_CASES_TAC `h2 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_INV_0]);;

e (REPEAT (POP_ASSUM MP_TAC));;
e (SIMP_TAC[z_tr_2d; INV_CPOW] THEN 
SIMP_TAC[INV_CPOW; COMPLEX_INV_INV; COMPLEX_POW_MUL;
         COMPLEX_FIELD `~(z1 = Cx (&0)) /\ ~(h1 = Cx (&0))
         ==>  ~(inv h1 * z1 = Cx(&0))`; 
     COMPLEX_FIELD `~(z2 = Cx (&0)) /\ ~(h2 = Cx (&0))
         ==>  ~(inv h2 * z2 = Cx(&0))`; CPOW_POW]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [GSYM CX_NEG]);;
e (REWRITE_TAC [CEXP_N]);;
e (ASM_SIMP_TAC [CEXP_CLOG]);;
e (REWRITE_TAC [CX_NEG]);;
e (REWRITE_TAC [COMPLEX_FIELD `!n. --Cx (&n) * a = -- (Cx (&n) * a)`]);;
e (REWRITE_TAC [CEXP_NEG]);;
e (REWRITE_TAC [CEXP_N]);;
e (ASM_SIMP_TAC [COMPLEX_FIELD `~(z1 = Cx (&0)) /\ ~(h1 = Cx (&0)) ==>  ~(inv h1 * z1 = Cx(&0))`; COMPLEX_FIELD `~(z2 = Cx (&0)) /\ ~(h2 = Cx (&0)) ==>  ~(inv h2 * z2 = Cx(&0))`; CEXP_CLOG]);;
e (REWRITE_TAC [COMPLEX_POW_MUL]);;
e (REWRITE_TAC [COMPLEX_INV_MUL]);;
e (REWRITE_TAC [GSYM COMPLEX_POW_INV]);;
e (REWRITE_TAC [COMPLEX_INV_INV]);;
e (SUBGOAL_THEN `!(n1:num) (n2:num).  ( (h1 pow n1 * h2 pow n2 * f n1 n2) * inv z1 pow n1 * inv z2 pow n2) = ( f n1 n2 * (h1 pow n1 * inv z1 pow n1) * h2 pow n2 * inv z2 pow n2)` ASSUME_TAC);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC []);;

let SCALING_2D_EXPAN_IN_Z1_Z2_DOAMIN = top_thm ();;

(*--------------------------------*)

g ` !f z1 z2 w1 w2. 
     z_tr_2d (\n1 n2. w1 cpow Cx(--(&n1)) * w2 cpow Cx(--(&n2)) * f n1 n2) z1 z2 = 
    (z_tr_2d (\n1 n2. f n1 n2) (w1 * z1) (w2 * z2))`;;

e (REPEAT GEN_TAC);;
e (ASM_CASES_TAC `z1 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]);;
e (ASM_CASES_TAC `z2 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]);;

e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]);;
e (ASM_CASES_TAC `w1 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_INV_0]);;
e (ASM_CASES_TAC `w2 = Cx(&0)`);;
e (ASM_SIMP_TAC[z_tr_2d; cpow; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_INV_0]);;

e (REPEAT (POP_ASSUM MP_TAC));;
e (SIMP_TAC[z_tr_2d; INV_CPOW] THEN 
SIMP_TAC[INV_CPOW; COMPLEX_INV_INV; COMPLEX_POW_MUL;
         COMPLEX_FIELD `~(z1 = Cx (&0)) /\ ~(w1 = Cx (&0))
         ==>  ~(inv w1 * z1 = Cx(&0))`; 
     COMPLEX_FIELD `~(z2 = Cx (&0)) /\ ~(w2 = Cx (&0))
         ==>  ~(inv w2 * z2 = Cx(&0))`; CPOW_POW]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [GSYM CX_NEG]);;
e (REWRITE_TAC [CEXP_N]);;
e (ASM_SIMP_TAC [CEXP_CLOG]);;
e (REWRITE_TAC [CX_NEG]);;
e (REWRITE_TAC [COMPLEX_FIELD `!n. --Cx (&n) * a = -- (Cx (&n) * a)`]);;
e (REWRITE_TAC [CEXP_NEG]);;
e (REWRITE_TAC [CEXP_N]);;
e (ASM_SIMP_TAC [COMPLEX_FIELD `~(z1 = Cx (&0)) /\ ~(w1 = Cx (&0)) ==>  ~(inv w1 * z1 = Cx(&0))`; COMPLEX_FIELD `~(z2 = Cx (&0)) /\ ~(w2 = Cx (&0)) ==>  ~(inv w2 * z2 = Cx(&0))`; CEXP_CLOG]);;
e (ASM_SIMP_TAC [COMPLEX_FIELD `~(z1 = Cx (&0)) /\ ~(w1 = Cx (&0)) ==>  ~(w1 * z1 = Cx(&0))`; COMPLEX_FIELD `~(z2 = Cx (&0)) /\ ~(w2 = Cx (&0)) ==>  ~(w2 * z2 = Cx(&0))`]);;
e (REWRITE_TAC [COMPLEX_POW_MUL]);;
e (REWRITE_TAC [COMPLEX_INV_MUL]);;
e (REWRITE_TAC [GSYM COMPLEX_POW_INV]);;
e (REWRITE_TAC [COMPLEX_INV_INV]);;
e (SUBGOAL_THEN `!(n1:num) (n2:num).  ( (inv w1 pow n1 * inv w2 pow n2 * f n1 n2) * inv z1 pow n1 * inv z2 pow n2) = ( f n1 n2 * (inv w1 pow n1 * inv z1 pow n1) * inv w2 pow n2 * inv z2 pow n2)` ASSUME_TAC);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC []);;

let SCALING_2D_SHRINK_IN_Z1_Z2_DOAMIN = top_thm ();;

(*---------------------------------------------*)

let CNJ_INFSUM = prove (
    `!f s. summable s f ==>  
    	infsum s (\n. cnj (f n)) = cnj (infsum s f)`,

REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN 
  REWRITE_TAC[SUMS_CNJ] THEN ASM_SIMP_TAC[SUMS_INFSUM]);;

g `!f z1 z2 (n1:num). (cnj z1, cnj z2) IN roc_2d f n1 ==>
         z_transform_2d (\n1 n2. cnj (f n1 n2)) z1 z2 = 
         cnj (z_transform_2d f (cnj z1) (cnj z2))`;;

e (SIMP_TAC[z_transform_2d; CNJ_DIV]);;
e (ONCE_REWRITE_TAC[MESON[CNJ_CNJ]` 
   !z n. z pow n = cnj (cnj (z pow n))`]);;
e (REWRITE_TAC [GSYM CNJ_MUL]);;
e (ONCE_REWRITE_TAC[GSYM CNJ_DIV]);;
e (REWRITE_TAC [CNJ_MUL]);;
e (ONCE_REWRITE_TAC[CNJ_POW]);;
e (ONCE_REWRITE_TAC[GSYM CNJ_POW;CNJ_CNJ]);;
e (REWRITE_TAC [CNJ_MUL]);;
e (ONCE_REWRITE_TAC[GSYM CNJ_POW;CNJ_CNJ]);;
e (REWRITE_TAC[GSYM CNJ_POW;CNJ_CNJ]);;
e (SIMP_TAC[roc_2d;IN_ELIM_THM]);;
e (REWRITE_TAC [GSYM CNJ_MUL]);;
e (ONCE_REWRITE_TAC[MESON[CNJ_CNJ]` 
   !z n1 n2.  f n1 n2 / cnj (z1 pow n1 * z2 pow n2) = 
         cnj(cnj(f n1 n2)) / cnj (z1 pow n1 * z2 pow n2)`]);;
e (REWRITE_TAC[GSYM CNJ_DIV]);;
e (ONCE_REWRITE_TAC[CNJ_MUL; GSYM CNJ_POW;CNJ_CNJ]);;
e (ONCE_REWRITE_TAC[MESON[CNJ_CNJ]` 
   !z n1 n2.  f n1 n2 / cnj (z1 pow n1 * z2 pow n2) = 
         cnj(cnj(f n1 n2))/ cnj (z1 pow n1 * z2 pow n2)`]);;
e (REWRITE_TAC [z_tr_sumable; z_tr_td_sumable]);;
e (REWRITE_TAC [GSYM CNJ_INV]);;
e (REWRITE_TAC [GSYM CNJ_POW]);;
e (REWRITE_TAC [GSYM CNJ_MUL]);;
e (REWRITE_TAC [COMPLEX_POW_INV]);;
e (REWRITE_TAC [GSYM COMPLEX_INV_MUL]);;
e (REWRITE_TAC [CNJ_INV]);;
e (REWRITE_TAC [GSYM complex_div]);;
e (REPEAT STRIP_TAC);;
      e (POP_ASSUM MP_TAC);;
      e (POP_ASSUM MP_TAC);;
      e (POP_ASSUM MP_TAC);;
      e (REWRITE_TAC [z_tr_summable; z_tr_td_summable]);;
      e (REPEAT STRIP_TAC);;

e (SUBGOAL_THEN `cnj
 (infsum (from 0)
 (\n1. infsum (from 0) (\n2. cnj (cnj (f n1 n2) / (z1 pow n1 * z2 pow n2))))) =
 (infsum (from 0)
 (\n1. cnj (infsum (from 0) (\n2. cnj (cnj (f n1 n2) / (z1 pow n1 * z2 pow n2))))))` ASSUME_TAC);;
      e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
      e (MATCH_MP_TAC CNJ_INFSUM);;
      e (REWRITE_TAC [summable]);;
      e (EXISTS_TAC `l:complex`);;
      e (ONCE_REWRITE_TAC[MESON[CNJ_CNJ]` 
   !z n1 n2.  cnj (cnj (f n1 n2) / (z1 pow n1 * z2 pow n2)) = 
         cnj (cnj (f n1 n2) / cnj (cnj (z1 pow n1 * z2 pow n2)))`]);;
      e (ONCE_REWRITE_TAC [GSYM CNJ_DIV]);;
      e (ASM_REWRITE_TAC [CNJ_CNJ]);;
      e (POP_ASSUM MP_TAC);;
      e (SIMP_TAC [PAIR_EQ]);;
      e (REWRITE_TAC [CNJ_MUL]);;
      e (REWRITE_TAC [CNJ_DIV]);;
      e (REWRITE_TAC [CNJ_POW]);;
      e (SIMP_TAC []);;
      e (REPEAT STRIP_TAC);;
      e (ASM_SIMP_TAC [complex_div]);;
      e (ASM_SIMP_TAC [COMPLEX_INV_MUL]);;
      e (ASM_SIMP_TAC [GSYM COMPLEX_POW_INV]);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC[MESON[CNJ_CNJ]` 
   !z1 z2 n1 n2.  cnj (cnj (f n1 n2) / (z1 pow n1 * z2 pow n2)) = 
         cnj (cnj (f n1 n2) / cnj (cnj (z1 pow n1 * z2 pow n2)))`]);;
e (ONCE_REWRITE_TAC [GSYM CNJ_DIV]);;
e (REWRITE_TAC [CNJ_CNJ]);;
e (SUBGOAL_THEN `!n1.  cnj (infsum (from 0) (\n2. f n1 n2 / cnj (z1 pow n1 * z2 pow n2))) = (infsum (from 0) (\n2. cnj (f n1 n2 / cnj (z1 pow n1 * z2 pow n2))))` ASSUME_TAC);;
      e (GEN_TAC);;
      e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
      e (MATCH_MP_TAC CNJ_INFSUM);;
      e (ASM_SIMP_TAC []);;
      e (POP_ASSUM MP_TAC);;
      e (SIMP_TAC [PAIR_EQ]);;
      e (REWRITE_TAC [CNJ_MUL]);;
      e (REWRITE_TAC [CNJ_DIV]);;
      e (REWRITE_TAC [CNJ_POW]);;
      e (SIMP_TAC []);;
      e (REPEAT STRIP_TAC);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [CNJ_DIV]);;
e (REWRITE_TAC [CNJ_CNJ]);;

let Z_TRANSFORM_2D_CNJ = top_thm ();; 

(*==============================================*)

let INFSUM_REINDEX = prove
   (`!f n k.  summable  (from n) (\x. f (x + k)) ==>
       infsum  (from (n+k)) f = infsum  (from n) (\x. f(x+k)) `,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE 
   THEN ASM_SIMP_TAC[GSYM SUMS_REINDEX;SUMS_INFSUM]);;

let SUMMABLE_OFFSET = prove 
 (`!f s n m. summable (from m)  f  /\  0 < n/\ m <= n ==> 
    summable (from n)  f`, MESON_TAC[LE_LT;summable;SUMS_OFFSET]);;

let SPEC_V (x,v) thm = (SPEC v o GEN x  o SPEC_ALL) thm;;


let   INFSUM_REINDEX_0 = prove
   (`!f k.  0 < k /\ summable  (from 0) f ==>
       infsum  (from k) f = infsum  (from 0) (\x. f(x+k)) `,
    MESON_TAC[REWRITE_RULE [ADD] (SPEC_V (`n:num`,`0`) INFSUM_REINDEX);
	SUMMABLE_REINDEX;ADD;LE_0;SUMMABLE_OFFSET]);;
		
let SUMMABLE_COMPLEX_LMUL = prove
  (`!c f s.  summable s f ==> summable s (\n. c*(f n)) `, 
   MESON_TAC[summable;SERIES_COMPLEX_LMUL]);;
   
let INFSUM_COMPLEX_LMUL = prove
  (`!c f s.  summable  s f ==> 
    infsum s (\n. c*(f n))  = c * infsum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE 
   THEN ASM_SIMP_TAC[GSYM SERIES_COMPLEX_LMUL;SUMS_INFSUM]);;
  
let INFSUM_OFFSET = prove
(`!f n m. summable  (from m) f 
   /\ 0 < n /\ m <= n ==> 
 infsum (from m)  f =
   vsum (m..n-1) f + infsum  (from n) f`,
 REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUMS_INFSUM] THEN
 DISCH_THEN(MP_TAC o MATCH_MP SUMS_OFFSET) THEN 
 MESON_TAC[VECTOR_ARITH `(x:complex) = y + z <=> z = x - y`;INFSUM_UNIQUE]);;

(*-------------------------------------------------------*)

let VSUM_OFFSET_0_NEG = prove
(`!f m n. m <= n ==> vsum(m..n) (\i.f (i-m)) = vsum(0..n - m) f`,
SIMP_TAC[VSUM_OFFSET_0;ADD_SUB]);;
 
let SERIES_RESTRICT_NUMSEG = prove
 (`!f k l:real^N.
        ((\n. if k <= n then f(n-k) else vec 0) sums l) (from 0) <=>
        ((\n.f(n-k)) sums l) (from k)`,
		 REWRITE_TAC[FROM_0] THEN
		 REWRITE_TAC[SPEC_V (`k:num->bool`,`from k`) (GSYM SERIES_RESTRICT)
	;IN;from;IN_ELIM_THM]);;

let SERIES_NEG_OFFSET = prove
 (`!f k l:real^N.
        (f sums l) (from 0) ==> ((\n.f(n-k)) sums l) (from k)`,
      	REWRITE_TAC[sums;LIM_SEQUENTIALLY;FROM_INTER_NUMSEG] THEN
	IMP_REWRITE_TAC[VSUM_OFFSET_0_NEG] THEN
	 MESON_TAC[ ARITH_RULE `N + k <= n ==> N <= n - k:num`
	 ;ARITH_RULE `N + k <= n ==> k:num <= n `]);;

let INFSUM_NEG_OFFSET = prove
 (`!f k. summable (from 0) f==> 
        infsum  (from 0) (\n. if k <= n then f(n-k) else vec 0) 
		   = infsum  (from 0) f`,
       REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
        REWRITE_TAC[SERIES_RESTRICT_NUMSEG] THEN
	MATCH_MP_TAC SERIES_NEG_OFFSET THEN 
	ASM_SIMP_TAC[SUMS_INFSUM]);;

let SERIES_RESTRICT = prove
 (`!f k l:real^N.
        ((\n. if n IN k then f(n) else vec 0) sums l) (:num) <=>
        (f sums l) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sums] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; INTER_UNIV] THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[] `vsum s f = vsum t f /\ vsum t f = vsum t g
                        ==> vsum s f = vsum t g`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN SET_TAC[];
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_INTER]]);;

let SERIES_RESTRICT_NUMSEG = prove
 (`!f k l:real^N.
        ((\n. if k <= n then f(n-k) else vec 0) sums l) (from 0) <=>
        ((\n.f(n-k)) sums l) (from k)`,
		 REWRITE_TAC[FROM_0] THEN
		 REWRITE_TAC[SPEC_V (`k:num->bool`,`from k`) (GSYM SERIES_RESTRICT)
	;IN;from;IN_ELIM_THM]);;

let INFSUM_NEG_OFFSET = prove
 (`!f k. summable (from 0) f==> 
        infsum  (from 0) (\n. if k <= n then f(n-k) else vec 0) 
		   = infsum  (from 0) f`,
       REPEAT STRIP_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
        REWRITE_TAC[SERIES_RESTRICT_NUMSEG] THEN
	MATCH_MP_TAC SERIES_NEG_OFFSET THEN 
	ASM_SIMP_TAC[SUMS_INFSUM]);;

let VSUM_OFFSET_0_NEG = prove
(`!f m n. m <= n ==> vsum(m..n) (\i.f (i-m)) = vsum(0..n - m) f`,
SIMP_TAC[VSUM_OFFSET_0;ADD_SUB]);;
  
let SERIES_NEG_OFFSET = prove
 (`!f k l:real^N.
        (f sums l) (from 0) ==> ((\n.f(n-k)) sums l) (from k)`,
      	REWRITE_TAC[sums;LIM_SEQUENTIALLY;FROM_INTER_NUMSEG] THEN
	IMP_REWRITE_TAC[VSUM_OFFSET_0_NEG] THEN
	 MESON_TAC[ ARITH_RULE `N + k <= n ==> N <= n - k:num`
	 ;ARITH_RULE `N + k <= n ==> k:num <= n `]);;

(*--------------------------------------------------------*)

(*==--Modeling the 2D generic difference equation for linear shift-invariant (LSI) System--==*)

let l1l2th_difference = new_definition
    `l1l2th_difference (f:num->num->complex) (c:num->num->complex) (L1:num) (L2:num) (n1:num) (n2:num) =
    vsum (0..L1) (\l1. vsum (0..L2) (\l2. (c l1 l2) * f (n1 - l1) (n2 - l2)))`;;


let VSUM_00 = prove
 (`vsum(0..0) f = f(0)`,
  REWRITE_TAC[VSUM_SING_NUMSEG]);;

let VSUM_11 = prove
 (`!t. vsum(0..1) t = t(0) + t(1)`,
  REWRITE_TAC[num_CONV `1`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;

let VSUM_22 = prove
 (`!t. vsum(0..2) t = t(0) + t(1) + t(2)`,
  REWRITE_TAC[num_CONV `1`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]);;

let VSUM_2 = prove
 (`!t. vsum(1..2) t = t(1) + t(2)`,
  REWRITE_TAC[num_CONV `1`; num_CONV `2`; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; ARITH; VECTOR_ADD_ASSOC]
  THEN VECTOR_ARITH_TAC);;


g `!f g z1 z2 n1.  
       z_tr_summable_cpow f z1 z2 n1 /\ 
       z_tr_summable_cpow g z1 z2 n1 
              ==> z_tr_summable_cpow (\n1 n2. f n1 n2 + g n1 n2) z1 z2 n1`;;

e (REWRITE_TAC[z_tr_summable_cpow] THEN 
REWRITE_TAC[COMPLEX_ADD_RDISTRIB] THEN
ASM_SIMP_TAC[SUMMABLE_ADD]);;

let Z_SUMMABLE_LINEAR = top_thm();;

g `!L2 L1 z1 z2 c (f:num->num->complex) n1.
 z_tr_summable_cpow f z1 z2 n1 /\ in_fst_quad_2d f
    ==> z_tr_summable_cpow (\n1 n2. vsum (0..L2)
       (\l2. (c (SUC L1) l2) * f (n1 - SUC L1) (n2 - l2))) z1 z2 n1`;;

e (INDUCT_TAC);;
e (REPEAT STRIP_TAC);;
e (SIMP_TAC [EL]);;;
e (SIMP_TAC [VSUM_00; EL]);;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;

e (REPEAT STRIP_TAC);;
e (SIMP_TAC [VSUM_00; EL]);;
e (ASM_SIMP_TAC [VSUM_CLAUSES_NUMSEG]);;
e (ASM_SIMP_TAC [ARITH_RULE `0 <= SUC L2`]);;
e (MATCH_MP_TAC Z_SUMMABLE_LINEAR);;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;

let DIFF_EQ_Z_SUMMABLE_ALT_LEMMA = top_thm ();;

g `!L1 L2 c f z1 z2 n1. z_tr_summable_cpow f z1 z2 n1 /\ 
                in_fst_quad_2d f 
     ==> z_tr_summable_cpow
           (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) z1 z2 n1`;;

e (INDUCT_TAC);;
e (INDUCT_TAC);;

e (SIMP_TAC [l1l2th_difference]);;
e (SIMP_TAC [EL]);;;
e (SIMP_TAC [VSUM_00; EL]);;
e (SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [l1l2th_difference]);;
e (SIMP_TAC [VSUM_00; EL]);;
e (ASM_SIMP_TAC [VSUM_CLAUSES_NUMSEG]);;
e (ASM_SIMP_TAC [ARITH_RULE `0 <= SUC L2`]);;
e (MATCH_MP_TAC Z_SUMMABLE_LINEAR);;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;
e (UNDISCH_TAC `!c:num->num->complex f:num->num->complex z1:complex z2:complex n1:num.
          z_tr_summable_cpow f z1 z2 n1 /\ in_fst_quad_2d f
          ==> z_tr_summable_cpow (\n1 n2. l1l2th_difference f c 0 L2 n1 n2) z1 z2 n1`);;
e (DISCH_THEN (MP_TAC o SPECL [`c:num->num->complex`; `f:num->num->complex`; `z1:complex`; `z2:complex`; `n1:num`]));;
e (ASM_SIMP_TAC [l1l2th_difference; VSUM_00; EL]);;

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [l1l2th_difference; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC L1`]);;
e (MATCH_MP_TAC Z_SUMMABLE_LINEAR);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [GSYM l1l2th_difference]);;
e (UNDISCH_TAC `!L2 (c:num->num->complex) (f:num->num->complex) z1 z2 n1. z_tr_summable_cpow f z1 z2 n1 /\ in_fst_quad_2d f
          ==> z_tr_summable_cpow (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) z1 z2 n1`);;
e (DISCH_THEN (MP_TAC o SPECL [`L2:num`; `c:num->num->complex`; `f:num->num->complex`; `z1:complex`; `z2:complex`; `n1:num`]));;
e (ASM_SIMP_TAC []);;
e (DISCH_TAC);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT_LEMMA]);;

let DIFF_EQ_Z_SUMMABLE_ALT = top_thm ();;

g `!f g z1 z2.
       z_tr_summable_cpow f z1 z2 n1 /\
       z_tr_summable_cpow g z1 z2 n1 /\
       z_tr_2d_summable_cpow f z1 z2 /\ 
       z_tr_2d_summable_cpow g z1 z2 
              ==> z_tr_2d_summable_cpow
	             (\n1 n2. f n1 n2 + g n1 n2) z1 z2`;;

e (REWRITE_TAC[z_tr_summable_cpow]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [z_tr_2d_summable_cpow]);;
e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (SUBGOAL_THEN `!n1. (infsum (from 0)
       (\n2. (f:num->num->complex) n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2) +
             g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2))) =
	    (infsum (from 0)
       (\n2. f n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)) +
       infsum (from 0)
       (\n2. g n1 n2 * z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2)))` ASSUME_TAC);;
      e (STRIP_TAC);;
      e (MATCH_MP_TAC INFSUM_ADD);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [GSYM summable]);;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [z_tr_2d_summable_cpow]);;
e (REWRITE_TAC [GSYM summable]);;
e (SIMP_TAC [SUMMABLE_ADD]);;

let Z_2D_SUMMABLE_LINEAR = top_thm();;

g `!f k1 k2 z1 z2. 
       z_tr_2d_summable_cpow f z1 z2 /\ 
       in_fst_quad_2d f
         ==> z_tr_2d_summable_cpow
	          (\x1 x2. f (x1 - k1) (x2 - k2)) z1 z2`;;

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `z_tr_2d_summable_cpow (\x1 x2. f (x1 - k1) (x2 - k2)) z1 z2 = z_tr_2d_summable_cpow (\x1 x2. Cx (&1) * f (x1 - k1) (x2 - k2)) z1 z2` ASSUME_TAC);;
      e (AP_THM_TAC);;
      e (AP_THM_TAC);;
      e (AP_TERM_TAC);;
      e (SUBGOAL_THEN `!x1 x2. ((f:num->num->complex) (x1 - k1) (x2 - k2)) = (Cx (&1) * f (x1 - k1) (x2 - k2))` ASSUME_TAC);;
            e (CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [COMPLEX_FIELD `Cx (&1) * x = x`]);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ASM_SIMP_TAC [Z_2D_SUMMABLE_CMUL_DIFF]);;

let Z_2D_SUMMABLE_CMUL_DIFF_SPEC = top_thm ();;

g `!f k1 k2 z1 z2 n1. 
       z_tr_summable_cpow f z1 z2 n1 /\ 
       in_fst_quad_2d f
         ==> z_tr_summable_cpow
	          (\x1 x2. f (x1 - k1) (x2 - k2)) z1 z2 n1`;;

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `z_tr_summable_cpow (\x1 x2. f (x1 - k1) (x2 - k2)) z1 z2 n1 = z_tr_summable_cpow (\x1 x2. Cx (&1) * f (x1 - k1) (x2 - k2)) z1 z2 n1` ASSUME_TAC);;
      e (AP_THM_TAC);;
      e (AP_THM_TAC);;
      e (AP_THM_TAC);;
      e (AP_TERM_TAC);;
      e (SUBGOAL_THEN `!x1 x2. ((f:num->num->complex) (x1 - k1) (x2 - k2)) = (Cx (&1) * f (x1 - k1) (x2 - k2))` ASSUME_TAC);;
            e (CONV_TAC COMPLEX_FIELD);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [COMPLEX_FIELD `Cx (&1) * x = x`]);;

e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;

let Z_SUMMABLE_CMUL_DIFF_SPEC = top_thm ();;

g `!L2 L1 c f z1 z2 n1.
       z_tr_summable_cpow f z1 z2 n1 /\
                in_fst_quad_2d f 
     ==> z_tr_summable_cpow
           (\n1 n2. vsum (0..L2) (\l2. (c L1 l2) * f (n1 - L1) (n2 - l2))) z1 z2 n1`;;

e (INDUCT_TAC);;

e (SIMP_TAC [EL]);;;
e (SIMP_TAC [VSUM_00; EL]);;
e (SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;

e (REPEAT STRIP_TAC);;
e (SIMP_TAC [VSUM_00; EL]);;
e (ASM_SIMP_TAC [VSUM_CLAUSES_NUMSEG]);;
e (ASM_SIMP_TAC [ARITH_RULE `0 <= SUC L2`]);;
e (MATCH_MP_TAC Z_SUMMABLE_LINEAR);;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;

let DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_1 = top_thm ();;


g `!L2 L1 c f z1 z2 n1.
       z_tr_2d_summable_cpow f z1 z2 /\
       z_tr_summable_cpow f z1 z2 n1 /\
                in_fst_quad_2d f 
     ==> z_tr_2d_summable_cpow
           (\n1 n2. vsum (0..L2) (\l2. (c L1 l2) * f (n1 - L1) (n2 - l2))) z1 z2`;;

e (INDUCT_TAC);;

e (SIMP_TAC [EL]);;;
e (SIMP_TAC [VSUM_00; EL]);;
e (SIMP_TAC [Z_2D_SUMMABLE_CMUL_DIFF]);;

e (REPEAT STRIP_TAC);;
e (SIMP_TAC [VSUM_00; EL]);;
e (ASM_SIMP_TAC [VSUM_CLAUSES_NUMSEG]);;
e (ASM_SIMP_TAC [ARITH_RULE `0 <= SUC L2`]);;
e (MATCH_MP_TAC Z_2D_SUMMABLE_LINEAR);;
e (ASM_SIMP_TAC [Z_2D_SUMMABLE_CMUL_DIFF; Z_SUMMABLE_CMUL_DIFF]);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_1]);;
e (UNDISCH_TAC `!L1:num c:num->num->complex f:num->num->complex z1:complex z2:complex n1:num.
          z_tr_2d_summable_cpow f z1 z2 /\
	  z_tr_summable_cpow f z1 z2 n1 /\
	  in_fst_quad_2d f
          ==> z_tr_2d_summable_cpow (\n1 n2. vsum (0..L2) (\l2. (c L1 l2) * f (n1 - L1) (n2 - l2))) z1 z2`);;
e (DISCH_THEN (MP_TAC o SPECL [`L1:num`; `c:num->num->complex`; `f:num->num->complex`; `z1:complex`; `z2:complex`; `n1:num`]));;
e (ASM_SIMP_TAC []);;

let DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_2 = top_thm ();;

g `!L1 L2 (c:num->num->complex) (f:num->num->complex) z1 z2 n1.
       z_tr_summable_cpow f z1 z2 n1 /\
       z_tr_2d_summable_cpow f z1 z2 /\ 
                in_fst_quad_2d f 
     ==> z_tr_2d_summable_cpow
           (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) z1 z2`;;

e (INDUCT_TAC);;
e (INDUCT_TAC);;

e (SIMP_TAC [l1l2th_difference]);;
e (SIMP_TAC [EL]);;;
e (SIMP_TAC [VSUM_00; EL]);;
e (SIMP_TAC [Z_2D_SUMMABLE_CMUL_DIFF]);;

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [l1l2th_difference]);;
e (SIMP_TAC [VSUM_00; EL]);;
e (ASM_SIMP_TAC [VSUM_CLAUSES_NUMSEG]);;
e (ASM_SIMP_TAC [ARITH_RULE `0 <= SUC L2`]);;
e (MATCH_MP_TAC Z_2D_SUMMABLE_LINEAR);;
e (REPEAT STRIP_TAC);;
r (1);;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF]);;
r (1);;
e (ASM_SIMP_TAC [Z_2D_SUMMABLE_CMUL_DIFF]);;

e (REPEAT STRIP_TAC);;
e (UNDISCH_TAC `!L2:num c:num->num->complex f:num->num->complex z1:complex z2:complex n1:num.
          z_tr_summable_cpow f z1 z2 n1 /\
	  z_tr_2d_summable_cpow f z1 z2 /\
	  in_fst_quad_2d f
          ==> z_tr_2d_summable_cpow
	     (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) z1 z2`);;
e (DISCH_THEN (MP_TAC o SPECL [`L2:num`; `c:num->num->complex`; `f:num->num->complex`; `z1:complex`; `z2:complex`; `n1:num`]));;
e (ASM_SIMP_TAC [l1l2th_difference; VSUM_00; EL]);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [l1l2th_difference; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC L1`]);;
e (MATCH_MP_TAC Z_2D_SUMMABLE_LINEAR);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [GSYM l1l2th_difference]);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT]);;
r (1);;
e (ASM_SIMP_TAC [GSYM l1l2th_difference]);;
e (MATCH_MP_TAC DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_2);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_1]);;
e (MATCH_MP_TAC DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_2);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_1]);;

let DIFF_EQ_Z_2D_SUMMABLE_ALT = top_thm ();;

g `!z1 z2 L1 L2 f c n1.
           (z1, z2) IN ROC_2d f (n1:num) /\
           in_fst_quad_2d f
      ==> (z1, z2) IN ROC_2d
                (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) n1`;;

e (REWRITE_TAC[IN; ROC_2d; IN_ELIM_THM]);;
e (REPEAT STRIP_TAC);;
e (EXISTS_TAC `z1':complex`);;
e (EXISTS_TAC `z2':complex`);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT]);;
e (MATCH_MP_TAC DIFF_EQ_Z_2D_SUMMABLE_ALT);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

let ROC_2D_DIFF_EQ = top_thm ();;

g `!(f:num->num->complex) (z1:complex) z2 L1 L2 c (n1:num). 
   z_tr_summable_cpow f z1 z2 n1 /\
   z_tr_2d_summable_cpow f z1 z2 /\
   in_fst_quad_2d f 
    ==>
   (z_tr_2d (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) z1 z2 =
        z_tr_2d f z1 z2 * vsum (0..L1)
    (\l1. vsum (0..L2) (\l2. z1 cpow (-- Cx(&l1)) * z2 cpow (-- Cx(&l2)) * (c l1 l2))))`;;

e (GEN_TAC THEN GEN_TAC THEN GEN_TAC);;

e (INDUCT_TAC);;
e (INDUCT_TAC);;
e (SIMP_TAC [VSUM_00; l1l2th_difference; EL; SUB; cpow; COMPLEX_MUL_RZERO; CEXP_NEG]);;
e (SIMP_TAC
      [COMPLEX_MUL_LZERO; CEXP_NEG; CEXP_0;
       COMPLEX_FIELD `--Cx (&0) * clog z = --(Cx (&0) * clog z)`;
       COMPLEX_FIELD `inv (Cx (&1)) = Cx (&1)`; COMPLEX_MUL_RID;
       COMPLEX_MUL_RID]);;
e (REPEAT STRIP_TAC);;
e (ASM_CASES_TAC `z1 = Cx (&0)`);;
e (ASM_CASES_TAC `z2 = Cx (&0)`);;
      e (ASM_SIMP_TAC []);;
      e (REWRITE_TAC [COMPLEX_FIELD `a * Cx (&0) * Cx (&0) * b = Cx (&0)`]);;
      e (REWRITE_TAC [z_tr_2d]);;
      e (SIMP_TAC [CPOW_0; COMPLEX_FIELD `a * Cx (&0) * Cx (&0) = Cx (&0)`]);;
      e (SIMP_TAC [GSYM COMPLEX_VEC_0; INFSUM_0]);;

      e (ASM_SIMP_TAC []);;
      e (REWRITE_TAC [COMPLEX_FIELD `a * Cx (&0) * Cx (&1) * b = Cx (&0)`]);;
      e (REWRITE_TAC [z_tr_2d]);;
      e (SIMP_TAC [CPOW_0; COMPLEX_FIELD `a * Cx (&0) * b = Cx (&0)`]);;
      e (SIMP_TAC [GSYM COMPLEX_VEC_0; INFSUM_0]);;

      e (ASM_CASES_TAC `z2 = Cx (&0)`);;
            e (ASM_SIMP_TAC []);;
      	    e (REWRITE_TAC [COMPLEX_FIELD `Cx (&1) * Cx (&0) * a = Cx (&0)`]);;
	    e (REWRITE_TAC [COMPLEX_FIELD `a * Cx (&0) = Cx (&0)`]);;
	    e (REWRITE_TAC [z_tr_2d]);;
      e (SIMP_TAC [CPOW_0; COMPLEX_FIELD `a * b * Cx (&0) = Cx (&0)`]);;
      e (SIMP_TAC [GSYM COMPLEX_VEC_0; INFSUM_0]);;

      e (ASM_SIMP_TAC []);;
      e (REWRITE_TAC [COMPLEX_FIELD `a * Cx (&1) * Cx (&1) * b = b * a`]);;
      e (SUBGOAL_THEN `(z_tr_2d (\n1 n2. c 0 0 * f n1 n2) z1 z2 = c 0 0 * z_tr_2d f z1 z2) = (z_tr_2d (\n1 n2. c 0 0 * f n1 n2) z1 z2 = c 0 0 * z_tr_2d (\n1 n2. f n1 n2) z1 z2)` ASSUME_TAC);;
            e (SIMP_TAC [ETA_AX]);;

      e (ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (MATCH_MP_TAC ZTR_2D_CONST_MUL);;
      e (EXISTS_TAC `n1:num`);;
      e (ASM_SIMP_TAC []);;

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC [l1l2th_difference; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC L2`]);;
e (SIMP_TAC [COMPLEX_ADD_LDISTRIB]);;
e (SUBGOAL_THEN `z_tr_2d f z1 z2 * z1 cpow --Cx (&0) * z2 cpow --Cx (&(SUC L2)) * (c 0 (SUC L2)) =
  z_tr_2d (\n1 n2. (c 0 (SUC L2)) * f (n1 - 0) (n2 - SUC L2)) z1 z2` ASSUME_TAC);;
      e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
      e (SUBGOAL_THEN `z_tr_2d (\n1 n2. (c 0 (SUC L2)) * f (n1 - 0) (n2 - SUC L2)) z1 z2 = (c 0 (SUC L2)) * z_tr_2d (\n1 n2. f (n1 - 0) (n2 - SUC L2)) z1 z2` ASSUME_TAC);;
            e (MATCH_MP_TAC ZTR_2D_CONST_MUL);;
	    e (EXISTS_TAC `n1:num`);;
	    e (ASM_SIMP_TAC [Z_2D_SUMMABLE_CMUL_DIFF_SPEC; Z_SUMMABLE_CMUL_DIFF_SPEC]);;

      e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
      e (SUBGOAL_THEN `z_tr_2d (\n1 n2. f (n1 - 0) (n2 - SUC L2)) z1 z2 = z1 cpow --Cx (&0) * z2 cpow --Cx (&(SUC L2)) * z_tr_2d f z1 z2` ASSUME_TAC);;
            e (MATCH_MP_TAC TIME_DELAY_2D_CPOW_ALT);;
	    e (EXISTS_TAC `n1:num`);;
	    e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `z_tr_2d f z1 z2 * vsum (0..L2) (\l2. z1 cpow --Cx (&0) * z2 cpow --Cx (&l2) * (c 0 l2)) = z_tr_2d (\n1 n2. vsum (0..L2) (\l2. (c 0 l2) * f (n1 - 0) (n2 - l2))) z1 z2` ASSUME_TAC);;
     e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

     r (1);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (MATCH_MP_TAC ZTR_2D_ADD);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC [Z_SUMMABLE_CMUL_DIFF; Z_2D_SUMMABLE_CMUL_DIFF]);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_1]);;
e (MATCH_MP_TAC DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_2);;
e (EXISTS_TAC `n1:num` THEN ASM_SIMP_TAC []);;

e (REPEAT STRIP_TAC);;
e (UNDISCH_TAC `!L2:num c:num->num->complex n1:num.
          z_tr_summable_cpow f z1 z2 n1 /\
          z_tr_2d_summable_cpow f z1 z2 /\
	  in_fst_quad_2d f
          ==> z_tr_2d (\n1 n2. l1l2th_difference f c L1 L2 n1 n2) z1 z2 = z_tr_2d f z1 z2 *
              vsum (0..L1)
              (\l1. vsum (0..L2)
                    (\l2. z1 cpow --Cx (&l1) * z2 cpow --Cx (&l2) * (c l1 l2)))`);;
e (DISCH_THEN (MP_TAC o SPECL [`L2:num`; `c:num->num->complex`; `n1:num`]));;
e (ASM_SIMP_TAC [] THEN STRIP_TAC);;
e (ASM_SIMP_TAC [l1l2th_difference; VSUM_CLAUSES_NUMSEG; ARITH_RULE `0 <= SUC L1`]);;
e (SIMP_TAC [COMPLEX_ADD_LDISTRIB]);;
e (SUBGOAL_THEN `z_tr_2d f z1 z2 *
 vsum (0..L2)
 (\l2. z1 cpow --Cx (&(SUC L1)) * z2 cpow --Cx (&l2) * (c (SUC L1) l2)) = z_tr_2d (\n1 n2.
      vsum (0..L2) (\l2. (c (SUC L1) l2) * f (n1 - SUC L1) (n2 - l2)))
 z1 z2` ASSUME_TAC);;
      e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;

      r (1);;

e (ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `z_tr_2d f z1 z2 *
 vsum (0..L1)
 (\l1. vsum (0..L2)
       (\l2. z1 cpow --Cx (&l1) * z2 cpow --Cx (&l2) * (c l1 l2))) =
        z_tr_2d
 (\n1 n2.
      vsum (0..L1)
      (\l1. vsum (0..L2) (\l2. (c l1 l2) * f (n1 - l1) (n2 - l2))))
 z1 z2` ASSUME_TAC);;
      e (ONCE_REWRITE_TAC [EQ_SYM_EQ]);;
      r (1);;

e (POP_ASSUM MP_TAC);;
e (SIMP_TAC []);;
e (DISCH_TAC);;
e (POP_ASSUM (K ALL_TAC));;

e (MATCH_MP_TAC ZTR_2D_ADD);;
e (EXISTS_TAC `n1:num`);;
e (REWRITE_TAC [GSYM l1l2th_difference]);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT]);;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC DIFF_EQ_Z_2D_SUMMABLE_ALT);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;
e (ASM_SIMP_TAC [DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_1]);;
e (MATCH_MP_TAC DIFF_EQ_Z_SUMMABLE_ALT_LEMMA_2);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

r (1);;
r (1);;

e (REWRITE_TAC [GSYM l1l2th_difference]);;
e (ASM_SIMP_TAC []);;

e (MATCH_MP_TAC Z_2D_SING_VSUM);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

e (MATCH_MP_TAC Z_2D_SING_VSUM);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

let ZTR_DIFFERENCE = top_thm ();;

(*===========================================================*)

let transfer_function_2d  =  new_definition ` 
    transfer_function_2d x y z1 z2 =
          z_tr_2d y z1 z2 / z_tr_2d x z1 z2`;;

let lccde_2d_new1 = define `
    lccde_2d_new1 x y a b M1 M2 N1 N2 n1 n2 <=> 
    (l1l2th_difference y b M1 M2 n1 n2) =
    (l1l2th_difference x a N1 N2 n1 n2)`;;


let lccde_roc_2d_new  = define `
  lccde_roc_2d_new g f M1 M2 c n1 = ROC_2d f n1 INTER ROC_2d g n1 DIFF 
    {(z1,z2) | (Cx (&1) -  vsum (0..M1) (\m1. vsum (0..M2)
    (\m2. (c m1 m2) * z1 cpow (--Cx(&m1)) * z2 cpow (--Cx(&m2))))) = 
    Cx(&0)}`;;


let in_fst_quad_lccde  = define `
    in_fst_quad_lccde x y  <=>  (in_fst_quad_2d x) /\
                                (in_fst_quad_2d y)`;;


let TRANS_FUN_TAC = ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      MATCH_MP_TAC ZTR_DIFFERENCE THEN EXISTS_TAC `n1:num`
      THEN ASM_REWRITE_TAC [];;


g `!(x:num->num->complex) y a b M1 M2 N1 N2 n1 z1 z2.
   z_tr_summable_cpow x z1 z2 n1 /\
   z_tr_2d_summable_cpow x z1 z2 /\
   z_tr_summable_cpow y z1 z2 n1 /\
   z_tr_2d_summable_cpow y z1 z2 /\
   ~(z1 = Cx (&0)) /\
   ~(z2 = Cx (&0)) /\
   ~(vsum (0..M1) (\m1. vsum (0..M2)
     (\m2. z1 cpow --Cx (&m1) * z2 cpow --Cx (&m2) * (b m1 m2))) =
              Cx (&0)) /\
   in_fst_quad_2d x /\
   in_fst_quad_2d y /\
    (!n1 n2. lccde_2d_new1 x y a b M1 M2 N1 N2 n1 n2) /\
    ~(z_tr_2d x z1 z2 = Cx (&0))
         ==> (transfer_function_2d x y z1 z2 =
            (vsum (0..N1) (\n1. vsum (0..N2)
       (\n2. z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2) * (a n1 n2))) /
            vsum (0..M1) (\m1. vsum (0..M2)
         (\m2. z1 cpow --Cx (&m1) * z2 cpow --Cx (&m2) * (b m1 m2)))))`;;

e (REWRITE_TAC [lccde_2d_new1; transfer_function_2d]);;
e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC
    [COMPLEX_FIELD
       `! a b c d. ~(d = Cx(&0)) /\  ~(b = Cx(&0)) ==> ( (a / b = c / d ) = (a*d = b*c ))`]);;

e (SUBGOAL_THEN `z_tr_2d y z1 z2 *
 vsum (0..M1)
 (\m1. vsum (0..M2)
       (\m2. z1 cpow --Cx (&m1) * z2 cpow --Cx (&m2) * b m1 m2)) = z_tr_2d (\n1 n2. l1l2th_difference_new y b M1 M2 n1 n2) z1 z2` ASSUME_TAC);;
      e (TRANS_FUN_TAC);;

e (ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `z_tr_2d x z1 z2 *
 vsum (0..N1)
 (\n1. vsum (0..N2)
       (\n2. z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2) * a n1 n2)) = z_tr_2d (\n1 n2. l1l2th_difference x a N1 N2 n1 n2) z1 z2` ASSUME_TAC);;
      e (TRANS_FUN_TAC);;

e (ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC));;

let TRANS_FUN_2D = top_thm ();;

(*==========--------------------======================*)
(*==Case study_Second-order image processing filter===*)
(*----------------------------------------------------*)

let second_order_ip_filter_new = new_definition
   `second_order_ip_filter_new x y a b n1 n2 =
    (l1l2th_difference y b 2 2 n1 n2 =
     l1l2th_difference x a 0 0 n1 n2)`;;

let DIFF_EQ_SIMP_TAC = REWRITE_TAC [EL; VSUM_00; VSUM_22] THEN
      ASM_SIMP_TAC [CPOW_POW] THEN
      REWRITE_TAC [COMPLEX_FIELD `-- Cx (&0) = Cx (&0)`] THEN
      ASM_SIMP_TAC [CPOW_N] THEN REWRITE_TAC [complex_pow] THEN
      CONV_TAC COMPLEX_FIELD;;

g `!(x:num->num->complex) y a b M1 M2 N1 N2 n1 z1 z2.
   z_tr_summable_cpow x z1 z2 n1 /\
   z_tr_2d_summable_cpow x z1 z2 /\
   z_tr_summable_cpow y z1 z2 n1 /\
   z_tr_2d_summable_cpow y z1 z2 /\
   ~(z1 = Cx (&0)) /\
   ~(z2 = Cx (&0)) /\
   in_fst_quad_2d x /\
   in_fst_quad_2d y /\
    (!n1 n2. second_order_ip_filter_new x y a b n1 n2) /\
    ~(z_tr_2d x z1 z2 = Cx (&0)) /\
    (a 0 0 = Cx (&1)) /\
    (b 0 0 = Cx (&1)) /\ (b 0 1 = -- b01) /\ (b 1 0 = -- b10) /\
    (b 1 1 = -- b11) /\ (b 0 2 = -- b02) /\ (b 1 2 = -- b12) /\
    (b 2 0 = -- b20) /\ (b 2 1 = -- b21) /\ (b 2 2 = -- b22) /\
    ~(((Cx (&1) -
  b01 * z2 cpow --Cx (&1) -
  b10 * z1 cpow --Cx (&1) -
  b11 * z1 cpow --Cx (&1) * z2 cpow --Cx (&1) -
  b02 * z2 cpow --Cx (&2) -
  b12 * z1 cpow --Cx (&1) * z2 cpow --Cx (&2) -
  b20 * z1 cpow --Cx (&2) -
  b21 * z1 cpow --Cx (&2) * z2 cpow --Cx (&1) -
  b22 * z1 cpow --Cx (&2) * z2 cpow --Cx (&2))) = Cx (&0))
    ==> (transfer_function_2d x y z1 z2 =
            (Cx (&1) / (Cx (&1) - b01 * z2 cpow (--Cx (&1)) -
	     b10 * z1 cpow (--Cx (&1)) -
	      b11 * z1 cpow (--Cx (&1)) * z2 cpow (--Cx (&1)) -
	     b02 * z2 cpow (--Cx (&2)) -
	      b12 * z1 cpow (--Cx (&1)) * z2 cpow (--Cx (&2)) -
	     b20 * z1 cpow (--Cx (&2)) -
	      b21 * z1 cpow (--Cx (&2)) * z2 cpow (--Cx (&1)) -
	     b22 * z1 cpow (--Cx (&2)) * z2 cpow (--Cx (&2))
	    )
	    ))`;;

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `(Cx (&1) -
  b01 * z2 cpow --Cx (&1) -
  b10 * z1 cpow --Cx (&1) -
  b11 * z1 cpow --Cx (&1) * z2 cpow --Cx (&1) -
  b02 * z2 cpow --Cx (&2) -
  b12 * z1 cpow --Cx (&1) * z2 cpow --Cx (&2) -
  b20 * z1 cpow --Cx (&2) -
  b21 * z1 cpow --Cx (&2) * z2 cpow --Cx (&1) -
  b22 * z1 cpow --Cx (&2) * z2 cpow --Cx (&2)) =
   (vsum (0..2) (\m1. vsum (0..2)
         (\m2. z1 cpow --Cx (&m1) * z2 cpow --Cx (&m2) * b m1 m2)))` ASSUME_TAC);;
      e (DIFF_EQ_SIMP_TAC);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (SUBGOAL_THEN `Cx (&1) =
   (vsum (0..0) (\n1. vsum (0..0)
         (\n2. z1 cpow --Cx (&n1) * z2 cpow --Cx (&n2) * a n1 n2)))` ASSUME_TAC);;
      e (DIFF_EQ_SIMP_TAC);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;

e (MATCH_MP_TAC TRANS_FUN_2D);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

e (UNDISCH_TAC `!n1 n2. second_order_ip_filter_new x y a b n1 n2`);;
e (SIMP_TAC [second_order_ip_filter_new; lccde_2d_new1]);;
e (DISCH_TAC);;
e (SUBGOAL_THEN `(vsum (0..2)
   (\m1. vsum (0..2) (\m2. z1 cpow --Cx (&m1) * z2 cpow --Cx (&m2) * b m1 m2))) = (Cx (&1) -
  b01 * z2 cpow --Cx (&1) -
  b10 * z1 cpow --Cx (&1) -
  b11 * z1 cpow --Cx (&1) * z2 cpow --Cx (&1) -
  b02 * z2 cpow --Cx (&2) -
  b12 * z1 cpow --Cx (&1) * z2 cpow --Cx (&2) -
  b20 * z1 cpow --Cx (&2) -
  b21 * z1 cpow --Cx (&2) * z2 cpow --Cx (&1) -
  b22 * z1 cpow --Cx (&2) * z2 cpow --Cx (&2))` ASSUME_TAC);;

      e (DIFF_EQ_SIMP_TAC);;

e (ASM_SIMP_TAC []);;

let TRANS_FUN_SEC_ORD_IPF_ALT = top_thm ();;

(*---------------------------------------------------*)

let cond_2d_diff_eq_coeff = new_definition `
   cond_2d_diff_eq_coeff (a:num->num->complex) (b:num->num->complex) b01 b10 b11 b02 b12 b20 b21 b22 = ((a 0 0 = Cx (&1)) /\
    (b 0 0 = Cx (&1)) /\ (b 0 1 = -- b01) /\ (b 1 0 = -- b10) /\
    (b 1 1 = -- b11) /\ (b 0 2 = -- b02) /\ (b 1 2 = -- b12) /\
    (b 2 0 = -- b20) /\ (b 2 1 = -- b21) /\ (b 2 2 = -- b22))`;;

let TF_denom_nz = new_definition `
    TF_denom_nz x z1 z2 b01 b10 b11 b02 b12 b20 b21 b22 =
  ( ~(((Cx (&1) -
  b01 * z2 cpow --Cx (&1) -
  b10 * z1 cpow --Cx (&1) -
  b11 * z1 cpow --Cx (&1) * z2 cpow --Cx (&1) -
  b02 * z2 cpow --Cx (&2) -
  b12 * z1 cpow --Cx (&1) * z2 cpow --Cx (&2) -
  b20 * z1 cpow --Cx (&2) -
  b21 * z1 cpow --Cx (&2) * z2 cpow --Cx (&1) -
  b22 * z1 cpow --Cx (&2) * z2 cpow --Cx (&2))) = Cx (&0)) /\
  ~(z_tr_2d x z1 z2 = Cx (&0)))`;;


g `!(x:num->num->complex) y a b M1 M2 N1 N2 n1 z1 z2 b01 b02 b10 b11 b12 b20 b21 b22.
   z_tr_summable_cpow x z1 z2 n1 /\
   z_tr_2d_summable_cpow x z1 z2 /\
   z_tr_summable_cpow y z1 z2 n1 /\
   z_tr_2d_summable_cpow y z1 z2 /\
   ~(z1 = Cx (&0)) /\
   ~(z2 = Cx (&0)) /\
   in_fst_quad_2d x /\
   in_fst_quad_2d y /\
    (!n1 n2. second_order_ip_filter_new x y a b n1 n2) /\
    TF_denom_nz x z1 z2 b01 b10 b11 b02 b12 b20 b21 b22 /\
    cond_2d_diff_eq_coeff a b b01 b10 b11 b02 b12 b20 b21 b22
    ==> (transfer_function_2d x y z1 z2 =
            (Cx (&1) / (Cx (&1) - b01 * z2 cpow (--Cx (&1)) -
	     b10 * z1 cpow (--Cx (&1)) -
	      b11 * z1 cpow (--Cx (&1)) * z2 cpow (--Cx (&1)) -
	     b02 * z2 cpow (--Cx (&2)) -
	      b12 * z1 cpow (--Cx (&1)) * z2 cpow (--Cx (&2)) -
	     b20 * z1 cpow (--Cx (&2)) -
	      b21 * z1 cpow (--Cx (&2)) * z2 cpow (--Cx (&1)) -
	     b22 * z1 cpow (--Cx (&2)) * z2 cpow (--Cx (&2))
	    )
	    ))`;;
	    
e (REWRITE_TAC [TF_denom_nz; cond_2d_diff_eq_coeff]);;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC TRANS_FUN_SEC_ORD_IPF_ALT);;
e (EXISTS_TAC `a:num->num->complex`);;
e (EXISTS_TAC `b:num->num->complex`);;
e (EXISTS_TAC `n1:num`);;
e (ASM_SIMP_TAC []);;

let TRANS_FUN_SEC_ORD_IPF = top_thm ();;

(*==========--------------------======================*)

