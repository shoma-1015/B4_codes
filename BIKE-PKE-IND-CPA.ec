(* ====================================================================
   BIKE PKE: IND-CPA security, on top of the QCCodes library

   Port of the machine-checked IND-CPA proof of BIKE-PKE (BIKE
   Specification v5.2, Appendix C.1) to EasyCrypt r2026.09. The ring,
   the Hamming weight, the error space E_t, key generation, the qcsd
   witness predicate and the OW-qcsd / qccf games come from the library
   (HammingWeight.eca, QCCodes.eca). This file keeps only what is specific
   to the IND-CPA argument: the message space, the random oracle L, the
   OW-CPA games under the real key, the game sequence of Table 13, the
   monitoring wrapper of Table 14 and the security proof.

   Reproduce ......... easycrypt compile -no-eco -p Alt-Ergo -I ~/PQC/library BIKE_PKE_IND_CPA.ec
   This copy (~/PQC/BIKE/r202609) uses PROM.FullRO for L, as IND-CCA2 needs.
   Main result ....... Theorem2_final (bottom of section Security)

   Correspondence with the specification
     PKE0 (Table 10)                   | PKE0.keyGen (library)
     qcsd(e,h,s) (Problem 3)           | wit / wit_spec (library)
     G3 (Table 11, left)               | G3_OW / G3_OW_S
     G4 (Table 11, middle)             | G4_OW_S (= OW_QCSD by G4_OW_S_eq)
     OW-qcsd game (Appendix B.1.1)     | OW_QCSD0 / OW_QCSD (library)
     qccf game                         | QCCF (library)
     distinguisher D (Table 11)        | D_cf
     G0 / G1 / G2 (Table 13)           | G0 / G1 / G2
     L' (Table 14), A0 (Table 14)      | Lmon, Red(A)
     Lemma 1, Theorems 1 and 2         | Lemma1, T1_false / T1_true,
                                       | Theorem2_concrete, Theorem2_final

   Intentional deviations (standard mechanization moves)
     (D1) Table 13's "stop and return true on a witness query" becomes a
          continuing bad flag (identical-until-bad).
     (D2) Pr[G2 | not L*] = 1/2 is proved as an equality via G2b (b moved
          to the tail) plus coin-flip symmetry.
     (D3) The unused sample of b in the paper's G3' is dropped in Red.
     (D4) qcsd is treated as the specification's OW (search) problem, so
          no hardness axiom is declared for it.
     (D5) The fit coercion for message length is discharged: under the
          adversary contract A_choose_wf, G0 equals the verbatim Table 13
          game G0_spec (lemma G0_G0_spec).

   Trust base: `print axiom.` lists gt0_r and l_ge0 (Top) and the
   parameter conditions of QCCodes.eca (QC), among them phi_irred and
   r_odd. Invertibility of the key-generation support (wt_unit) is a
   lemma derived from these two, not an axiom. The adversary contract
   declared in section Security (A_choose_ll, A_guess_ll, A_choose_wf)
   appears as hypotheses of Theorem2_final. No hardness axiom is
   declared.
   ==================================================================== *)

require import AllCore IntDiv List Distr DBool FMap.
require PROM DynMatrix QCCodes.

op r : int. op w : int. op t : int. op l : int.

axiom gt0_r : 0 < r.
axiom l_ge0 : 0 <= l.

clone import QCCodes as QC with
  op r <- r, op w <- w, op t <- t
proof gt0_r by exact gt0_r.

lemma dEt_t_ll : is_lossless (dEt t).
proof. by apply dEt_ll; smt(t_ge0 t_le_n). qed.

(* ====================================================================
   1. MESSAGE SPACE M = F_2^l
   --------------------------------------------------------------------
   Messages are vectors over F2. The type carries no length, hence the
   coercion fit and the adversary contract A_choose_wf below.
   ==================================================================== *)
clone import DynMatrix as Matrix with
  theory ZR <= Zp.ZModpRing.

type M = vector.

op dM : M distr = dvector Zp.DZmodP.dunifin l.

(* ====================================================================
   2. RANDOM ORACLE L : Rn x Rn -> M
   ==================================================================== *)
(* PROM.FullRO rather than ROM.Lazy, so that the eager/lazy toolkit is
   available for the T-transform hop of the IND-CCA2 proof
   (BIKE_KEM_IND_CCA2.ec). PROM.FullRO.RO.get has the body of
   ROM.Lazy.LRO.o, so the proofs below are unchanged up to renaming. *)
clone PROM.FullRO as ROL with
  type in_t  <- Rn * Rn,
  type out_t <- M,
  op   dout  <- fun _ => dM.
module L = {
  proc init(): unit = { ROL.RO.init(); }
  proc hash(x : Rn * Rn): M = { var y; y <@ ROL.RO.get(x); return y; }
}.


(* Losslessness of the sampling distributions and of the oracles. *)
lemma duniformM_ll : is_lossless dM.
proof. rewrite /dM; apply dvector_ll; exact Zp.DZmodP.dunifin_ll. qed.
lemma L_hash_ll : islossless L.hash.
proof. proc; inline ROL.RO.get; auto => />; smt(duniformM_ll). qed.
lemma L_hash_eq :
  equiv[ L.hash ~ L.hash : ={arg, ROL.RO.m} ==> ={res, ROL.RO.m} ].
proof. by proc; inline ROL.RO.get; auto. qed.
(* One-time pad helpers over M, used for the rnd coupling in Step 2 and
   in G2b. They amount to: v |-> m + v is a measure-preserving bijection
   of dM, which is exactly what the three side conditions of the
   rnd tactic ask for. *)
lemma duniformM_size (v : M) : v \in dM => size v = l.
proof.
  rewrite /dM => hv.
  have := size_dvector Zp.DZmodP.dunifin l v hv.
  smt(l_ge0).
qed.

lemma vec_subrK (m v : M) : size m = l => size v = l => m + (v - m) = v.
proof.
  move=> hm hv.
  have e1 : v - m = -m + v by apply Vectors.addvC.
  rewrite e1 Vectors.addvA.
  have e2 : m + -m = zerov l.
  + have := Vectors.addvN m.
    rewrite hm => ->; reflexivity.
  rewrite e2.
  have := Vectors.add0v v.
  rewrite hv => ->; reflexivity.
qed.

lemma vec_subrK2 (m v : M) : size m = l => size v = l => m + v - m = v.
proof.
  move=> hm hv.
  rewrite (Vectors.addvC m v) -Vectors.addvA.
  have e2 : m + -m = zerov l.
  + have h := Vectors.addvN m. rewrite hm in h. exact h.
  rewrite e2.
  have hlv : l = size v by rewrite hv.
  by rewrite (Vectors.lin_addv0 v l hlv).
qed.

lemma vec_subv_supp (m v : M) :
  size m = l => v \in dM => (v - m) \in dM.
proof.
  move=> hm hv.
  have hsz : size v = l by apply duniformM_size.
  have hl : 0 <= l by smt(l_ge0).
  rewrite /dM (supp_dvector Zp.DZmodP.dunifin (v - m) l hl).
  rewrite size_addv size_oppv hsz hm /=.
  split; first smt().
  move=> i hi.
  rewrite get_addv getvN.
  exact Zp.DZmodP.dunifin_fu.
qed.

lemma duniformM_funi (v1 v2 : M) :
  size v1 = l => size v2 = l => mu1 dM v1 = mu1 dM v2.
proof.
  move=> h1 h2; rewrite /dM.
  rewrite -{1}h1 -{1}h2 !mu1_dvector_fu; first exact Zp.DZmodP.dunifin_funi.
  + exact Zp.DZmodP.dunifin_funi.
  by rewrite h1 h2.
qed.

(* fit pads a message into F_2^l. It mechanizes the specification's
   "m in F_2^l", since the type M = vector carries no length.

   Deviation D5 is discharged by fit_id below: fit is the identity on
   well-formed messages, so for any adversary that returns messages in
   {0,1}^l -- the only adversaries the specification quantifies over --
   the game G0 is literally Table 13's G0. For other adversaries fit acts
   as the challenger's input coercion. *)
op fit (m : M) : M = offunv ((fun i => m.[i]), l).

lemma size_fit (m : M) : size (fit m) = l.
proof. by rewrite /fit size_offunv; smt(l_ge0). qed.

lemma fit_id (m : M) : size m = l => fit m = m.
proof.
move=> hm; rewrite /fit.
apply/eq_vectorP; split.
+ by rewrite size_offunv hm; smt(l_ge0).
move=> i; rewrite size_offunv => hi.
by rewrite get_offunv 1:/#.
qed.


(* ====================================================================
   3. OW-CPA UNDER THE REAL KEY (Table 11) AND THE DISTINGUISHER D
   ==================================================================== *)

(* Table 11, left: OW-CPA under the real key. *)
module G3_OW (A0 : QCSD_Solver) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* Spec-faithful twins of the two OW games, with wit replaced by
   wit_spec. *)
module G3_OW_S (A0 : QCSD_Solver) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit_spec (oget eo) h s);
  }
}.

lemma G3_OW_spec_eq (A0 <: QCSD_Solver) &m :
  Pr[G3_OW(A0).main() @ &m : res] = Pr[G3_OW_S(A0).main() @ &m : res].
proof.
byequiv (: ={glob A0} ==> ={res}) => //.
proc.
seq 1 1 : (={glob A0, h} /\ parity h{2} = 1).
+ by call keyGen_eq_odd.
call (_: true).
auto => />.
smt(wit_spec_equiv).
qed.

(* Table 11, middle, verbatim: (h0, h1) <- Hw is sampled and never used.
   The OW-qcsd advantage of Appendix B.1.1 has no such sample, so the
   proofs below work with OW_QCSD directly; G4_OW_S_eq justifies this. *)
module G4_OW_S (A0 : QCSD_Solver) = {
  proc main() : bool = {
    var h0, h1, h, e0e1, s, eo;
    h0 <$ dWt d;
    h1 <$ dWt d;
    h <$ dRodd;
    e0e1 <$ dEt t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit_spec (oget eo) h s);
  }
}.

(* Step 2 of the proof of Theorem 1: Adv_G4(A0) = Adv^OW_qcsd(A0). The
   unused key sample is lossless, so it can be dropped. *)
lemma G4_OW_S_eq (A0 <: QCSD_Solver) &m :
  Pr[G4_OW_S(A0).main() @ &m : res] = Pr[OW_QCSD(A0).main() @ &m : res].
proof.
byequiv (: ={glob A0} ==> ={res}) => //.
proc.
call (: true).
wp; rnd; rnd.
rnd{1}; rnd{1}.
auto => />; smt(dWt_d_ll).
qed.

(* Table 11, right: the qccf distinguisher, that is lines 3 to 6 of G4. *)
module D_cf (A0 : QCSD_Solver) = {
  proc distinguish(h : Rn) : bool = {
    var e0e1, s, eo;
    e0e1 <$ (dEt t);
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.


(* ====================================================================
   4. IND-CPA GAME SEQUENCE (Table 13) AND MONITORING WRAPPER (Table 14)
   ==================================================================== *)
module type OrclL = { proc hash(_ : Rn * Rn) : M }.

module type LOR_Adv (O : OrclL) = {
  proc choose(h : Rn) : M * M        {O.hash}  (* A1(h) -> (m0,m1,st) *)
  proc guess(c0 : Rn, c1 : M) : bool {O.hash}  (* A2(h,c0,c1,st) -> b';
                                                 h and st live in glob A *)
}.

module BadWit = {
  var h  : Rn
  var c0 : Rn
  var wt : (Rn * Rn) option
}.

(* L' of Table 14: record the witness query, then forward to L. *)
module Lmon : OrclL = {
  proc hash(e : Rn * Rn) : M = {
    var v;
    if (wit e BadWit.h BadWit.c0) { BadWit.wt <- Some e; }
    v <@ L.hash(e);
    return v;
  }
}.

(* G0: IND-CPA, Table 13 left, without instrumentation. *)
module G0 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);                 (* e*  *)
    c0 <- e0e1.`1 + e0e1.`2 * h;                   (* c0* *)
    b <$ {0,1};
    m0m1 <@ A(L).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- fit (b ? m0m1.`2 : m0m1.`1) + lv;
    b' <@ A(L).guess(c0, c1);
    return b' = b;
  }
}.

(* G0_spec: Table 13's G0 verbatim, without the fit coercion. Under the
   well-formedness contract A_choose_wf the two games are equal, see
   G0_G0_spec, which is what discharges deviation D5. *)
module G0_spec (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);
    c0 <- e0e1.`1 + e0e1.`2 * h;
    b <$ {0,1};
    m0m1 <@ A(L).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- (b ? m0m1.`2 : m0m1.`1) + lv;
    b' <@ A(L).guess(c0, c1);
    return b' = b;
  }
}.

(* G1: G0 plus the L* instrumentation. Only the adversary's queries are
   watched; the challenger keeps using the raw oracle L. *)
module G1 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    b <$ {0,1};
    m0m1 <@ A(Lmon).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- fit (if b then m0m1.`2 else m0m1.`1) + lv;
    b' <@ A(Lmon).guess(c0, c1);
    return b' = b;
  }
}.

(* G2: the second ciphertext component is uniform, Table 13 right. *)
module G2 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, c1, b';
    L.init();
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    b <$ {0,1};
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ dM;
    b' <@ A(Lmon).guess(c0, c1);
    return b' = b;
  }
}.

(* G2b: G2 with b moved to the tail, for the 1/2 argument of deviation
   D2. This is sound because in G2 the bit b is unused until the
   return. *)
module G2b (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, c1, b';
    L.init();
    h <@ PKE0.keyGen();
    e0e1 <$ (dEt t);
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ dM;
    b' <@ A(Lmon).guess(c0, c1);
    b <$ {0,1};
    return b' = b;
  }
}.

(* Red(A): the adversary A0 of Table 14. It recovers the recorded witness
   and returns it. The paper's unused sample of b is dropped, see
   deviation D3. *)
module Red (A : LOR_Adv) : QCSD_Solver = {
  proc solve(h : Rn, s : Rn) : (Rn * Rn) option = {
    var m0m1, c1, b';
    L.init();
    BadWit.h <- h; BadWit.c0 <- s; BadWit.wt <- None;
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ dM;
    b' <@ A(Lmon).guess(s, c1);
    return BadWit.wt;
  }
}.

(* ====================================================================
   5. SECURITY
   ==================================================================== *)
section Security.

declare module A <: LOR_Adv {-PKE0, -L, -ROL.RO, -BadWit}.

(* No computational hardness axiom is declared in this file. The results
   below are exact-probability statements relative to the concrete games
   played by the explicit reductions Red(A) and D_cf(Red(A)); see the
   trust base in the header. The main claim is Theorem2_final, with
   Lemma1_spec connecting the real-key parity chain. *)

declare axiom A_choose_ll : forall (O <: OrclL {-A}),
  islossless O.hash => islossless A(O).choose.
declare axiom A_guess_ll : forall (O <: OrclL {-A}),
  islossless O.hash => islossless A(O).guess.

(* Well-formedness contract: A returns messages in F_2^l. This is exactly
   the quantification of the specification, whose adversaries output
   m0, m1 in {0,1}^l; adversaries violating it are outside the model. *)
declare axiom A_choose_wf (O <: OrclL {-A}) :
  hoare[ A(O).choose : true ==> size res.`1 = l /\ size res.`2 = l ].

(* Lmon is lossless, which is needed for the one-sided handling after
   the bad event. *)
lemma Lmon_hash_ll : islossless Lmon.hash.
proof. proc; call L_hash_ll; auto. qed.

(* --------------------------------------------------------------------
   Step 1: G0 and G1 are identical (transparency of the
   instrumentation).
   -------------------------------------------------------------------- *)

(* A_choose_wf lifted to a self-equivalence, with both sides in sync and
   the size information carried along. *)
lemma A_choose_eq_wf :
  equiv[ A(L).choose ~ A(L).choose :
         ={arg, glob A, ROL.RO.m} ==>
         ={res, glob A, ROL.RO.m}
         /\ size res{2}.`1 = l /\ size res{2}.`2 = l ].
proof.
conseq (: ={arg, glob A, ROL.RO.m} ==> ={res, glob A, ROL.RO.m})
       _ (A_choose_wf L) => //.
proc (={ROL.RO.m}) => //.
exact L_hash_eq.
qed.

(* Closure of deviation D5: for well-formed adversaries fit is the
   identity, so G0 equals the spec game G0_spec. *)
lemma G0_G0_spec &m :
  Pr[G0(A).main() @ &m : res] = Pr[G0_spec(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (_: ={ROL.RO.m}); first exact L_hash_eq.
wp.
call L_hash_eq.
call A_choose_eq_wf.
rnd.
wp.
rnd.
call keyGen_eq.
inline L.init ROL.RO.init.
auto => />.
smt(fit_id).
qed.

lemma G0_G1 &m :
  Pr[G0(A).main() @ &m : res] = Pr[G1(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (_: ={ROL.RO.m}).
+ by proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto => />.
wp.
call L_hash_eq.
call (_: ={ROL.RO.m}).
+ by proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto => />.
rnd.
wp.
rnd.
call keyGen_eq.
inline L.init ROL.RO.init.
auto => />.
qed.

(* --------------------------------------------------------------------
   Step 2: if L* does not occur then G1 and G2 are identical. This is a
   single-bad up-to-bad argument and is the core of the proof.

   Structure. Two preservation lemmas first (each side stays bad once it
   is bad), then the up-to-bad equivalence G1_G2_upto, then its two
   corollaries.

   How G1_G2_upto works. The invariant used by the three-argument form of
   call is

     ={BadWit.h, BadWit.c0, BadWit.wt, glob A, ...}
     /\ eq_except (pred1 e_star) ROL.RO.m{1} ROL.RO.m{2}

   and each oracle call produces four side goals: the equivalence itself
   plus two one-sided losslessness goals that must preserve the
   invariant. Preservation is immediate because BadWit.wt is only ever
   overwritten by Some, hence monotone.

   The middle of the game is the challenge: the left side runs
   lv <@ L.hash(e_star) and sets c1 <- m_b + lv, while the right side
   samples c1 <$ dM. The postcondition of the call for choose has
   shape "if bad{2} then invariant else joined", so the proof splits on
   BadWit.wt{2} <> None:

     not bad: from the invariant "not bad implies e_star is not yet in
       the domain of the ROM map" -- bad is exactly "a witness was
       queried", e_star is a witness, and this is before the challenger
       writes -- the left-hand hash takes its sampling branch, and the
       fresh sample is coupled with the right-hand one by rnd with the
       involution v |-> m_b + v (see the one-time pad helpers of
       Section 2). Afterwards the two ROM maps agree except at e_star,
       which is the eq_except part of the invariant.

     bad: both sides are run losslessly, preserving BadWit.wt and hence
       re-establishing the invariant.

   The prefix (init, keyGen, e_star, c0, the BadWit assignments and b)
   runs
   in sync. In the postcondition, equality of the bad flags follows from
   the joined branch on the not-bad side and from the invariant on the
   bad side.
   -------------------------------------------------------------------- *)
lemma A_guess_pres :
  phoare[ A(Lmon).guess : BadWit.wt <> None ==> BadWit.wt <> None ] = 1%r.
proof.
conseq (: true ==> true) (: BadWit.wt <> None ==> BadWit.wt <> None) => //.
+ proc (BadWit.wt <> None) => //.
  by proc; inline*; auto => />; smt().
by apply (A_guess_ll Lmon Lmon_hash_ll).
qed.

lemma L_hash_pres :
  phoare[ L.hash : BadWit.wt <> None ==> BadWit.wt <> None ] = 1%r.
proof. by proc; inline*; auto => />; smt(duniformM_ll). qed.

lemma G1_G2_upto :
  equiv[ G1(A).main ~ G2(A).main :
         ={glob A} ==>
         (BadWit.wt{1} <> None) = (BadWit.wt{2} <> None)
         /\ (BadWit.wt{2} = None => ={res}) ].
proof.
proc.
(* the prefix, instructions 1 to 8, runs in sync *)
seq 8 8 : (={glob A, ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt,
             h, e0e1, c0, b}
           /\ BadWit.wt{2} = None
           /\ BadWit.h{2} = h{2} /\ BadWit.c0{2} = c0{2}
           /\ wit e0e1{2} h{2} c0{2}
           /\ e0e1{2} \notin ROL.RO.m{2}).
+ inline L.init ROL.RO.init.
  auto.
  call keyGen_eq.
  auto => />.
  smt(Et_filter mem_empty).
(* turn e* into a logical constant: oracle invariants cannot mention
   program variables *)
exists* e0e1{2}; elim* => estar.
(* the up-to-bad call for choose *)
seq 1 1 : (if BadWit.wt{2} <> None
           then BadWit.wt{1} <> None /\ BadWit.wt{2} <> None
           else ={glob A, ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt,
                  b, e0e1, c0, m0m1}
                /\ BadWit.wt{2} = None
                /\ wit estar BadWit.h{2} BadWit.c0{2}
                /\ e0e1{2} = estar
                /\ estar \notin ROL.RO.m{2}).
+ call (_: BadWit.wt <> None,
        ={ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ wit estar BadWit.h{2} BadWit.c0{2}
        /\ (BadWit.wt{2} = None => estar \notin ROL.RO.m{2}),
          BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).

  + exact A_choose_ll.
  (* oracle equivalence, under the not-bad precondition *)
  + proc.
    if => //.
    + (* witness branch *)
      inline L.hash ROL.RO.get.
      sp.
      seq 1 1 : (={x0, ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt}
                 /\ BadWit.wt{2} <> None).
      + by auto => />; smt().
      if => //.
      + by auto => />; smt().
      by auto => />; smt().
    (* non-witness branch *)
    inline L.hash ROL.RO.get.
    sp.
    seq 1 1 : (={e, x0, r, ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt}
               /\ x0{2} = e{2}
               /\ wit estar BadWit.h{2} BadWit.c0{2}
               /\ (BadWit.wt{2} = None => estar \notin ROL.RO.m{2})
               /\ !wit e{2} BadWit.h{2} BadWit.c0{2}).
    + by auto => />; smt().
    if => //.
    + by auto => />; smt(mem_set get_setE).
    by auto => />; smt().
  (* losslessness after bad, left side *)
  + move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
  (* losslessness after bad, right side *)
  + move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
  (* discharge of the prefix *)
  auto => />; smt().
(* split on bad *)
case (BadWit.wt{2} <> None).
(* bad branch: run both sides losslessly *)
+ conseq (: _ ==> BadWit.wt{1} <> None /\ BadWit.wt{2} <> None) => //; 1: smt().
  call{1} A_guess_pres.
  call{2} A_guess_pres.
  wp.
  rnd{2}.
  call{1} L_hash_pres.
  auto => />; smt(duniformM_ll).
(* not-bad branch: the one-time pad coupling *)
(* the left-hand call L.hash(e_star) takes its sampling branch, since
   e_star is not
   yet in the ROM map *)
inline{1} L.hash ROL.RO.get.
rcondt{1} 4.
+ by auto => />; smt().
(* the up-to-bad call for guess *)
call (_: BadWit.wt <> None,
      ={BadWit.h, BadWit.c0, BadWit.wt}
      /\ eq_except (pred1 estar) ROL.RO.m{1} ROL.RO.m{2}
      /\ wit estar BadWit.h{2} BadWit.c0{2},
        BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).

  + exact A_guess_ll.
(* oracle equivalence: in the witness branch the postcondition only
   concerns the then-side, while the non-witness branch stays in sync via
   eq_except *)
+ proc.
  if => //.
  + (* witness branch, which triggers bad: both sides have set
       BadWit.wt to Some e, so the inner conditionals may be out of
       sync *)
    inline L.hash ROL.RO.get.
    sp.
    seq 1 1 : (BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).
    + by auto => />; smt().
    if{1}; if{2}; by auto => />; smt().
  (* non-witness branch: e differs from estar, so eq_except keeps the
     conditionals in sync *)
  inline L.hash ROL.RO.get.
  sp.
  seq 1 1 : (={e, x0, r, BadWit.h, BadWit.c0, BadWit.wt}
             /\ x0{2} = e{2}
             /\ eq_except (pred1 estar) ROL.RO.m{1} ROL.RO.m{2}
             /\ wit estar BadWit.h{2} BadWit.c0{2}
             /\ !wit e{2} BadWit.h{2} BadWit.c0{2}).
  + by auto => />; smt().
  if.
  + by move=> &1 &2 />; smt(eq_exceptP domE).
  + by auto => />; smt(eq_exceptP eq_except_set_eq get_setE get_set_sameE mem_set domE).
    by auto => />; smt(eq_exceptP domE).
(* losslessness after bad, left side *)
+ move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
(* losslessness after bad, right side *)
+ move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
(* the one-time pad coupling: the fresh ROM sample on the left against
   c1 on the right *)
wp.
rnd (fun (v : M) => fit (if b{1} then m0m1{1}.`2 else m0m1{1}.`1) + v)
    (fun (c : M) => c - fit (if b{1} then m0m1{1}.`2 else m0m1{1}.`1)).
auto => />.
smt(vec_subrK vec_subrK2 vec_subv_supp duniformM_funi duniformM_size
    size_fit size_addv size_oppv
    get_set_sameE oget_some eq_except_setl eq_exceptP).
qed.

lemma G1_G2_res_notbad &m :
  Pr[G1(A).main() @ &m : res /\ BadWit.wt = None]
  = Pr[G2(A).main() @ &m : res /\ BadWit.wt = None].
proof. by byequiv G1_G2_upto => // /#. qed.

lemma G1_G2_bad &m :
  Pr[G1(A).main() @ &m : BadWit.wt <> None]
  = Pr[G2(A).main() @ &m : BadWit.wt <> None].
proof. by byequiv G1_G2_upto => // /#. qed.

(* --------------------------------------------------------------------
   Step 3: Pr[G2 | not L*] = 1/2, mechanized as an equality, see
   deviation D2.

   (a) Move b to the tail, which is sound because b is unused until the
       return: swap plus sim, transported for the two events
       "res and not bad" and "not bad".
   (b) Coin-flip symmetry: at the tail, rnd with the involution
       x |-> !x on {0,1}; everything before it is sim. Both "not bad" and
       b' are fixed before b is sampled, so the two events simply swap.
   (c) Sum: Pr[E] = Pr[res /\ E] + Pr[not res /\ E].
   -------------------------------------------------------------------- *)
lemma G2_G2b_res_notbad &m :
  Pr[G2(A).main() @ &m : res /\ BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : res /\ BadWit.wt = None].
proof.
byequiv (: ={glob A} ==> ={res} /\ ={BadWit.wt}) => //.
by proc; swap{1} 8 3; sim.
qed.

lemma G2_G2b_notbad &m :
  Pr[G2(A).main() @ &m : BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : BadWit.wt = None].
proof.
byequiv (: ={glob A} ==> ={res} /\ ={BadWit.wt}) => //.
by proc; swap{1} 8 3; sim.
qed.

lemma G2b_flip &m :
  Pr[G2b(A).main() @ &m : res /\ BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : !res /\ BadWit.wt = None].
proof.
byequiv (: ={glob A} ==>
           (res{1} /\ BadWit.wt{1} = None)
           <=> (!res{2} /\ BadWit.wt{2} = None)) => //.
proc.
seq 10 10 : (={ROL.RO.m, BadWit.wt, b'}); first by sim.
rnd (fun (x : bool) => !x).
auto => />.
smt(dbool1E dbool_fu).
qed.

lemma G2b_split &m :
  Pr[G2b(A).main() @ &m : BadWit.wt = None]
  = Pr[G2b(A).main() @ &m : res /\ BadWit.wt = None]
  + Pr[G2b(A).main() @ &m : !res /\ BadWit.wt = None].
proof.
rewrite Pr [mu_split res].
congr.
+ by rewrite Pr [mu_eq] => /#.
by rewrite Pr [mu_eq] => /#.
qed.

lemma half_split &m :
  Pr[G2(A).main() @ &m : res /\ BadWit.wt = None]
  = 1%r/2%r * Pr[G2(A).main() @ &m : BadWit.wt = None].
proof.
  rewrite (G2_G2b_res_notbad &m) (G2_G2b_notbad &m).
  have hf := G2b_flip &m. have hs := G2b_split &m. smt().
qed.

(* --------------------------------------------------------------------
   Step 4: 1/2 - p/2 <= Pr[G0] <= 1/2 + p/2, where p = Pr[L*].

   Split the result event of G1 on the bad flag and squeeze, using the
   equalities of Steps 2 and 3 together with
   0 <= Pr[res /\ bad] <= Pr[bad]. This step is pure arithmetic.
   -------------------------------------------------------------------- *)
lemma G2_full &m : Pr[G2(A).main() @ &m : true] = 1%r.
proof.
byphoare => //.
proc.
call (A_guess_ll Lmon Lmon_hash_ll).
rnd.
call (A_choose_ll Lmon Lmon_hash_ll).
rnd.
wp.
rnd.
call keyGen_ll.
inline L.init ROL.RO.init.
auto => />.
smt(duniformM_ll dEt_t_ll dbool_ll).
qed.

lemma G0_half_bound &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G2(A).main() @ &m : BadWit.wt <> None].
proof.
have h01    := G0_G1 &m.
have hres   := G1_G2_res_notbad &m.
have hbad   := G1_G2_bad &m.
have hhalf  := half_split &m.
have hfull  := G2_full &m.
have hsplit : Pr[G1(A).main() @ &m : res]
  = Pr[G1(A).main() @ &m : res /\ BadWit.wt = None]
  + Pr[G1(A).main() @ &m : res /\ BadWit.wt <> None].
+ by rewrite Pr [mu_split (BadWit.wt = None)].
have hcompl : Pr[G2(A).main() @ &m : true]
  = Pr[G2(A).main() @ &m : BadWit.wt = None]
  + Pr[G2(A).main() @ &m : BadWit.wt <> None].
+ rewrite Pr [mu_split (BadWit.wt = None)].
  by congr; rewrite Pr [mu_eq] => /#.
have hub : Pr[G1(A).main() @ &m : res /\ BadWit.wt <> None]
        <= Pr[G1(A).main() @ &m : BadWit.wt <> None].
+ by rewrite Pr [mu_sub] => /#.
have hf0 : Pr[G1(A).main() @ &m : false] = 0%r by rewrite Pr [mu_false].
have h0  : Pr[G1(A).main() @ &m : false]
        <= Pr[G1(A).main() @ &m : res /\ BadWit.wt <> None].
+ by rewrite Pr [mu_sub].
smt().
qed.

(* --------------------------------------------------------------------
   Step 5: Pr[G3'] = Pr[L*], that is, the bad probability of G2 equals
   the success probability of the OW reduction.

   The invariant is
     ={glob A, glob L, BadWit.h, BadWit.c0, BadWit.wt}
     /\ (BadWit.wt <> None => wit (oget BadWit.wt) BadWit.h BadWit.c0)
   which is preserved because Lmon only ever records witnesses; it turns
   the result of G3_OW into the bad flag. The bit b exists only in G2, on
   the left-hand side, and its sampling is consumed by rnd{1}.
   -------------------------------------------------------------------- *)
lemma G2_bad_Red &m :
  Pr[G2(A).main() @ &m : BadWit.wt <> None]
  = Pr[G3_OW(Red(A)).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> (BadWit.wt{1} <> None) <=> res{2}) => //.
proc.
inline{2} Red(A).solve.
inline L.init ROL.RO.init.
wp.
call (_: ={ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ (BadWit.wt{2} <> None =>
              wit (oget BadWit.wt{2}) BadWit.h{2} BadWit.c0{2})).
+ by proc; call L_hash_eq; auto => />; smt().
rnd.
call (_: ={ROL.RO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ (BadWit.wt{2} <> None =>
              wit (oget BadWit.wt{2}) BadWit.h{2} BadWit.c0{2})).
+ by proc; call L_hash_eq; auto => />; smt().
rnd{1}.
wp.
rnd.
call keyGen_eq.
auto => />.
smt(dbool_ll).
qed.

(* --------------------------------------------------------------------
   Lemma 1 of the specification: Adv^IND-CPA <= 1/2 * Adv^OW-CPA, with
   the reduction Red(A).
   -------------------------------------------------------------------- *)
lemma Lemma1 &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G3_OW(Red(A)).main() @ &m : res].
proof.
  have h1 := G0_half_bound &m. have h2 := G2_bad_Red &m. smt().
qed.

(* --------------------------------------------------------------------
   Theorem 1 of the specification:
     Adv^OW-CPA_PKE0 <= Adv^IND_qccf + Adv^OW_qcsd.
   The two halves are the false and the true branch of QCCF.
   -------------------------------------------------------------------- *)
lemma T1_false (A0 <: QCSD_Solver) &m :
  Pr[G3_OW(A0).main() @ &m : res]
  = Pr[QCCF(D_cf(A0)).main(false) @ &m : res].
proof.
byequiv (: ={glob A0} /\ b{2} = false ==> ={res}) => //.
proc.
inline{2} D_cf(A0).distinguish.
wp.
call (_: true).
wp.
rnd.
wp.
rnd{2}.
call keyGen_eq.
auto => />.
smt(dRodd_ll).
qed.

lemma T1_true (A0 <: QCSD_Solver) &m :
  Pr[OW_QCSD0(A0).main() @ &m : res]
  = Pr[QCCF(D_cf(A0)).main(true) @ &m : res].
proof.
byequiv (: ={glob A0} /\ b{2} = true ==> ={res}) => //.
proc.
inline{2} D_cf(A0).distinguish.
wp.
call (_: true).
wp.
rnd.
wp.
rnd.
call{2} keyGen_ll.
auto => />.
qed.

(* --------------------------------------------------------------------
   Theorem 2, concrete-security form: the advantage bound stated against
   the two concrete games for the specific reductions Red(A) and
   D_cf(Red(A)), with no hardness axiom.

   Writing eps_qccf for the qccf advantage of D_cf(Red(A)) and
   eps_qcsd_ow for the OW success probability of Red(A), this is exactly
   the bound of Theorem 2,

     Adv <= 1/2 * eps_qccf + 1/2 * eps_qcsd_ow,

   and T1_false together with T1_true is Theorem 1. The computational
   reading -- both epsilons are negligible for efficient A, because
   Red(A) and D_cf(Red(A)) are efficient whenever A is -- is prose; no
   hardness axiom is declared in this file.

   This is the G0-side statement, kept for the correspondence with the
   specification. The spec-side main claim Theorem2_final is derived
   independently, via Lemma1_spec.
   -------------------------------------------------------------------- *)
lemma Theorem2_concrete &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[QCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[QCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[OW_QCSD0(Red(A)).main() @ &m : res].
proof.
have h1 := Lemma1 &m.
have hf := T1_false (Red(A)) &m.
have ht := T1_true (Red(A)) &m.
smt().
qed.

(* The same bound with the OW term stated against the spec-faithful game
   OW_QCSD, which uses wit_spec, via OW_QCSD0_eq. *)
lemma Theorem2_concrete_spec &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[QCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[QCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[OW_QCSD(Red(A)).main() @ &m : res].
proof.
have h := Theorem2_concrete &m.
have he := OW_QCSD0_eq (Red(A)) &m.
smt().
qed.

(* Lemma 1 in fully spec-faithful form. This is where the real-key parity
   chain -- keyGen_eq_odd, and behind it wt_d_odd, parity_invr and
   wt_unit (QCCodes.eca) -- enters the claim, through G3_OW_spec_eq. *)
lemma Lemma1_spec &m :
  `| Pr[G0_spec(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G3_OW_S(Red(A)).main() @ &m : res].
proof.
have h0 := G0_G0_spec &m.
have h1 := Lemma1 &m.
have h2 := G3_OW_spec_eq (Red(A)) &m.
smt().
qed.

(* MAIN CLAIM.

   Theorem2_final is derived from Lemma1_spec: the real-key leg is the
   spec-faithful game G3_OW_S, which carries the keyGen parity chain and
   is converted back to G3_OW by G3_OW_spec_eq for the Theorem 1
   bridges, and the uniform-key leg is OW_QCSD. Both sides of the
   statement are therefore the verbatim games of the specification, and
   the only axioms involved are the adversary contract and the parameter
   conditions listed in the header. *)
lemma Theorem2_final &m :
  `| Pr[G0_spec(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[QCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[QCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[OW_QCSD(Red(A)).main() @ &m : res].
proof.
have h1 := Lemma1_spec &m.
have h2 := G3_OW_spec_eq (Red(A)) &m.
have hf := T1_false (Red(A)) &m.
have ht := T1_true (Red(A)) &m.
have he := OW_QCSD0_eq (Red(A)) &m.
smt().
qed.

end section Security.
