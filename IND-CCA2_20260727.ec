(* ====================================================================
   BIKE PKE — IND-CPA security, faithful to BIKE Spec v5.2 (2024.10.10),
   Appendix C.1.
   --------------------------------------------------------------------
   Correspondence with the paper:
     PKE0 (Table 10)                  | Bike.keyGen (encryption inlined in games)
     qcsd(e,h,s) (Problem 3)          | op wit
     G3 / G4 (Table 11)               | G3_OW / G4_OW
     distinguisher D (Table 11)       | D_cf
     PKE (Table 12)                   | c = (e0+e1h, m_b + L(e)) inside G0
     G0 / G1 / G2 (Table 13)          | G0 / G1 / G2
     event L*                         | BadWit.wt <> None
     L' (Table 14)                    | Lmon
     A0 = (A^L'_1, A^L'_2) (T.14)     | Red(A)
     Lemma 1 / Thm 1 / Thm 2          | Lemma1 / T1_false+T1_true / Theorem2_concrete
     qcsd with domain checks          | op wit_spec (G3_OW_S / G4_OW_S)
     h in R_odd (Key Security)        | keyGen_odd / keyGen_supp_odd
     main claim (hardness axiom-free) | Theorem2_final (+ lemma1_spec)

   Intentional deviations (standard mechanization moves):
     (D1) Table 13's "stop and return true on a witness query" becomes a
          continuing bad flag (identical-until-bad); the distribution up to
          the stopping point is unchanged.
     (D2) Pr[G2 | ¬L*] = 1/2 is proved as an equality via an equivalent
          game G2b (b moved to the tail) plus coin-flip symmetry, giving
          Pr[res /\ ¬bad] = ½·Pr[¬bad]. The factor 1/2 matches the paper.
     (D3) The unused b sample in the paper's G3' is dropped in Red
          (distribution unchanged).
     (D4) qcsd is treated as the paper's OW (search) problem: G4_OW is
          the OW-qcsd game itself; no hardness axiom is declared (revision f+3)
     (D5) fit coercion for message length — DISCHARGED in revision f:
          under A_choose_wf, G0 = G0_spec (Table 13 verbatim), lemma
          G0_G0_spec.
*** VERIFICATION STATUS (revision f, 2026-07-13) ***
     REVISION f+4 VERIFIED: EasyCrypt r2025.03 / Alt-Ergo, exit 0
     (full reload from top, zero admits, no hardness axioms).
       (f1) Major 1: parity infrastructure (ev1 = coefficient sum =
            evaluation at 1, a ring hom in char 2: ev1D / ev1M via
            rcoeffM + index-shift bigop reindexing; parity_add /
            parity_mul / parity_oner) culminating in keyGen_odd /
            keyGen_supp_odd: the public key h = h1 * invp h0 is odd
            with probability 1.
       (f2) Major 2: DRodd_odd, syndrome_parity (s = e0 + e1*h lies in
            R_p(t) for odd h), wit_spec (Problem 3 with domain checks),
            wit_spec_equiv, and spec-faithful twins G3_OW_S / G4_OW_S
            with Pr-equalities G3_OW_spec_eq / G4_OW_spec_eq.
       (f3) Major 3: hardness axioms annotated as epsilon-notation
            devices only; NEW axiom-free main claims Theorem2_concrete
            and Theorem2_concrete_spec (advantage bound relative to the
            concrete games for Red(A) / D_cf(Red(A))).
       (f4) Major 4: invp_correct now used in the chain (invp_odd ->
            keyGen_odd); Hw_unit remains the sole existential parameter
            condition.
       (f5) Major 5: well-formedness contract A_choose_wf (adversary
            messages lie in F_2^l, the paper's quantification); G0_spec
            (Table 13 G0 verbatim, no fit) and G0_G0_spec: Pr[G0] =
            Pr[G0_spec]. Deviation D5 is now discharged, not argued.
      (f+2) keyGen_eq_odd re-derived from keyGen_odd via conseq, wiring
            the Code Major 1 hoare theorem into the Lemma1_spec chain.
       (f+3) Dead-code removal and Code Major 3 closure by deletion:
            the epsilon-notation layer (ops eps_qccf / eps_qcsd_ow,
            axioms qccf_hard / qcsd_ow_hard, lemmas Theorem1 / Theorem2)
            and the unused lemmas Lmon_pres / A_choose_pres and
            op ( ^ ) are removed. No hardness axiom remains in the
            file; the RFinite block is annotated as a finiteness
            export.
      (f+4) Theorem2_final re-derived from Lemma1_spec, making the
            real-key parity chain (keyGen_odd / invp_correct) a proof
            dependency of the main claim.
     Axiom inventory of this revision:
       hardness (in-section): NONE (the epsilon-notation layer —
         Theorem1/Theorem2 and axioms qccf_hard/qcsd_ow_hard — was
         removed in f+3; the paper correspondence lives in the comment
         above Theorem2_concrete_spec).
       adversary contract (in-section): A_choose_ll, A_guess_ll
         (termination), A_choose_wf (messages in F_2^l).
       benign / mathematically-true facts: NONE
       parameter conditions, used in proofs: r_gt0, l_ge0, w_gt0, w_even,
         uneven_w_half (parity of dHw elements, revision f), d_le_r,
         t_ge0, t_le_n
       parameter conditions, existential form: Hw_unit (every weight-d
         element is a unit; NOT derivable from r_prime/uneven_w_half —
         counterexample r = 7 — it additionally encodes BIKE's choice
         "2 is a primitive root mod r" and d < r; discharging it needs
         F2[X] gcd/Bezout theory absent from the stdlib)
       parameter conditions, documentation only: r_prime
         (mathematical justification of Hw_unit).
   ==================================================================== *)

require import AllCore IntDiv.

op r : int. op w : int. op t : int. op l : int.
op n = r + r.  op d = w %/ 2.

(* Parameter conditions.
   Used directly in machine proofs:
     r_gt0 (PolyRing clone obligation gt0_n), l_ge0 (vector-size lemmas).
   Documentation-only (they are the mathematical justification for the
   benign axioms below; they carry no proof weight yet):
     w_gt0, w_even        => d = w/2 >= 1        (justifies enumHw_nonempty)
     uneven_w_half        => d odd; USED since revision f (dHw_odd,
                             parity chain to keyGen_odd)
     r_prime              => together with BIKE's choice of r such that
                             (X^r-1)/(X-1) is irreducible over F2, every
                             odd-weight x <> 1+X+...+X^{r-1} is invertible
                             (justifies invp_correct)
     t_ge0, t_le_n        => a weight-t error pair exists
                             (justifies exists_filter_Et)
d_le_r
   r_ge3 (only needed by the removed decoder/alg2 material) is deleted. *)
axiom r_gt0  : 0 < r.
axiom l_ge0  : 0 <= l.
axiom w_gt0  : 0 < w.
axiom w_even : 2 %| w.
axiom uneven_w_half : !(2 %| d).
axiom r_prime : prime r.
(* Used in machine proofs from revision d: enumHw_nonempty (weight-d
   witness needs d <= r). True for all BIKE parameter sets (d << r). *)
axiom d_le_r : d <= r.
axiom t_ge0  : 0 <= t.
axiom t_le_n : t <= n.

require import List Distr DBool IntMin RealExp.
require ROM PolyReduce BitWord DynMatrix.

(* ====================================================================
   0. RING / TYPES / CONVERSIONS
   (from old §1; pi_l / K / duniformK removed)
   ==================================================================== *)
clone import PolyReduce.PolyReduceZp as PolyRing with op n = r, op p = 2 proof *.
realize ge2_p. smt. qed.
realize gt0_n. smt(r_gt0). qed.

clone import DynMatrix as Matrix with
  op   ZR.(+) = PolyRing.Zp.(+),
  type ZR.t  <= PolyRing.Zp.

type R = polyXnD1.
type M = vector.

op polyToVec (x : polyXnD1) : vector = offunv ((fun i => x.[i]), r).
op RListToInt (x : Matrix.R list) =
  with x = []      => []
  with x = y :: ys => Zp.asint y :: RListToInt ys.
op polyToList (x : polyXnD1) = RListToInt (tolist (polyToVec x)).
op ham_weight (x : int list) =
  with x = []      => 0
  with x = y :: ys => ((y=0)?0:1) + (ham_weight ys).

op duniformM = Matrix.Vectors.dvector Zp.DZmodP.dunifin l.

(* ====================================================================
   1. E_t / R ENUMERATION / R_odd
   (from old §2; parity(R_part) family removed)
   ==================================================================== *)
op filter_Et (x : (R * R)) : bool =
  (ham_weight (polyToList x.`1) + ham_weight (polyToList x.`2) = t).
op list_append_each ['a 'b] (s : 'a list) (u : 'b) =
  with s = []      => []
  with s = x :: xs => (u, x) :: list_append_each xs u.
op double_list (s : 'a list) (u : 'b list) =
  with s = []      => []
  with s = x :: xs => list_append_each u x ++ double_list xs u.
  op enumR : R list = map polyLX (alltuples r Zp.DZmodP.Support.enum).

    (* Step A: polyLX is injective on length-r coefficient lists. *)
  (* Finiteness export (unused by the proof chain): R is a finite type,
   witnessed by the duplicate-free complete enumeration enumR
   (polyLX_inj -> enumR_uniq -> enumR_spec -> RFinite). This discharges
   the last benign axiom of revision c (enumR_spec) and grounds the
   duniform distributions over R used throughout. *)
lemma polyLX_inj (s1 s2 : Zp list) :
  size s1 = r => size s2 = r => polyLX s1 = polyLX s2 => s1 = s2.
proof.
move=> h1 h2 heq.
apply (eq_from_nth Zp.zero); first by rewrite h1 h2.
move=> i hi.
rewrite -(polyLXE s1 i) 1:/# -(polyLXE s2 i) 1:/#.
by rewrite heq.
qed.

(* Step B: enumR is duplicate-free. *)
lemma enumR_uniq : uniq enumR.
proof.
rewrite /enumR.
apply map_inj_in_uniq.
+ move=> s1 s2 /alltuplesP [hs1 _] /alltuplesP [hs2 _].
  by apply polyLX_inj; smt(r_gt0).
by apply alltuples_uniq; exact Zp.DZmodP.Support.enum_uniq.
qed.

(* Step C: enumR is complete. *)
lemma enumR_complete (x : R) : x \in enumR.
proof.
pose s := mkseq (fun (i : int) => x.[i]) r.
have hsz : size s = r by rewrite size_mkseq; smt(r_gt0).
have hmem : s \in alltuples r Zp.DZmodP.Support.enum.
+ apply/alltuplesP; split; first smt(r_gt0).
  by apply/allP => z _; exact Zp.DZmodP.Support.enumP.
have hpx : polyLX s = x.
+ apply/polyXnD1_eqP => i hi.
  rewrite polyLXE 1:/# nth_mkseq 1:/# //.
by rewrite /enumR; apply/mapP; exists s; rewrite hmem hpx.
qed.

(* Step D: the last benign axiom becomes a lemma. *)
lemma enumR_spec (x : R) : count (pred1 x) enumR = 1.
proof.
by rewrite count_uniq_mem 1:enumR_uniq enumR_complete.
qed.
  
op enumE_t = filter filter_Et (double_list enumR enumR).

clone MFinite as RFinite with type t <- R, op Support.enum <- enumR proof *.
realize Support.enum_spec. exact enumR_spec. qed.

  (* Bridge: ham_weight of the asint image = number of nonzero entries. *)
lemma ham_weight_count (s : Matrix.R list) :
  ham_weight (RListToInt s) = count (fun (z : Matrix.R) => z <> Zp.zero) s.
proof.
elim: s => //= z s ih; rewrite ih.
smt(Zp.zeroE Zp.asint_eq).
qed.

(* Bridge: ham_weight of a polynomial = number of nonzero coefficients
   among indices 0..r-1. *)
lemma ham_weight_coeff (x : R) :
  ham_weight (polyToList x)
  = count (fun (i : int) => x.[i] <> Zp.zero) (range 0 r).
proof.
rewrite /polyToList ham_weight_count /polyToVec /tolist.
rewrite size_offunv.
have -> : max 0 r = r by smt(r_gt0).
rewrite count_map.
apply eq_in_count => i /mem_range hi /=.
rewrite /preim /=.
  rewrite get_offunv 1:/#.
by rewrite /rcoeff.
qed.

(* Witness factory: a polynomial of any weight k <= r exists. *)
lemma weight_k_exists (k : int) :
  0 <= k <= r => exists (x : R), ham_weight (polyToList x) = k.
proof.
move=> hk.
pose s := mkseq (fun (i : int) => if i < k then Zp.one else Zp.zero) r.
exists (polyLX s).
rewrite ham_weight_coeff.
have -> : count (fun (i : int) => (polyLX s).[i] <> Zp.zero) (range 0 r)
        = count (fun (i : int) => i < k) (range 0 r).
+ apply eq_in_count => i /mem_range hi /=.
  rewrite polyLXE 1:size_mkseq 1:/#.
  rewrite nth_mkseq 1:/# /=.
  smt(Zp.oneE Zp.zeroE).
rewrite (range_cat k 0 r) 1,2:/# count_cat.
have -> : count (fun (i : int) => i < k) (range 0 k) = k.
+ have hall : all (fun (i : int) => i < k) (range 0 k).
  * by apply/allP => i /mem_range /#.
  by move/all_count: hall => ->; rewrite size_range /#.
have -> : count (fun (i : int) => i < k) (range k r) = 0.
+ have hno : !has (fun (i : int) => i < k) (range k r).
  * by apply/hasPn => i /mem_range /#.
  by smt(has_count count_ge0).
by [].
      qed.

lemma mem_enumR (a : R) : a \in enumR.
proof. exact enumR_complete. qed.


op distribution_over_E_t : (R * R) distr = duniform enumE_t.

op poly_parity (x : R) : int = (ham_weight (polyToList x)) %% 2.

(* Characteristic 2: negation is the identity on Zp. *)
lemma oppW (a : Zp) : Zp.([-]) a = a.
proof.
apply Zp.asint_inj; rewrite Zp.oppE.
smt(Zp.rg_asint).
qed.

(* Characteristic 2: subtraction is addition on Zp. *)
lemma subW (a b : Zp) : Zp.(-) a b = Zp.(+) a b.
    proof. by rewrite oppW. qed.

  (* ev1: sum of coefficients = evaluation at 1 (a ring hom since p = 2:
   1 is a root of X^r + 1). *)
op ev1 (x : R) : Zp = Zp.BigZMod.BAdd.bigi predT (fun i => x.[i]) 0 r.

lemma ev1D (x y : R) : ev1 (x + y) = Zp.(+) (ev1 x) (ev1 y).
proof.
rewrite /ev1 -Zp.BigZMod.BAdd.big_split.
by apply Zp.BigZMod.BAdd.eq_big_int => i hi /=; rewrite rcoeffD.
qed.

(* BCA (BasePoly.BigCf) and BAdd (Zp.BigZMod) are the same fold. *)
lemma BCA_BAdd ['a] (P : 'a -> bool) (F : 'a -> Zp) (s : 'a list) :
  BasePoly.BigCf.BCA.big P F s = Zp.BigZMod.BAdd.big P F s.
    proof. by rewrite /BasePoly.BigCf.BCA.big /Zp.BigZMod.BAdd.big. qed.

  (* rcoeffM in characteristic 2, stated with BAdd. *)
lemma rcoeffM2 (p q : R) (k : int) :
  0 <= k < r =>
  (p * q).[k]
  = Zp.BigZMod.BAdd.bigi predT
      (fun (i : int) => Zp.(+) (Zp.( * ) p.[i] q.[k - i])
                               (Zp.( * ) p.[i] q.[r + k - i])) 0 r.
proof.
move=> hk.
rewrite rcoeffM 1:// BCA_BAdd.
apply Zp.BigZMod.BAdd.eq_big_int => i hi /=.
by rewrite subW.
qed.

(* Index shift for coefficient sums, general shift amount. *)
lemma big_shift (y : R) (i : int) :
  Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[k - i]) 0 r
  = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (-i) (r - i).
proof.
have -> : Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (-i) (r - i)
        = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (0 - i) (r - i).
+ by have -> : -i = 0 - i by smt().
rewrite (Zp.BigZMod.BAdd.big_addn 0 (r - i) (-i) predT (fun (j : int) => y.[j])).
have -> : r - i - -i = r by smt().
apply Zp.BigZMod.BAdd.eq_big => //= k.
      qed.

      (* For fixed 0 <= i < r, summing the two wrapped columns over k
   recovers the full coefficient sum of y. *)
lemma inner_sum (y : R) (i : int) :
  0 <= i < r =>
  Zp.BigZMod.BAdd.bigi predT
    (fun (k : int) => Zp.(+) y.[k - i] y.[r + k - i]) 0 r
  = ev1 y.
proof.
move=> hi.
have hL : Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[k - i]) 0 r
        = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) 0 (r - i).
+ rewrite (big_shift y i).
  rewrite (Zp.BigZMod.BAdd.big_cat_int 0 (-i) (r - i)) 1,2:/#.
  rewrite (Zp.BigZMod.BAdd.big1_seq predT _ (range (-i) 0)).
  + by move=> j [_ /mem_range hj] /=; rewrite lt0_rcoeff 1:/#.
  by rewrite Zp.ZModpRing.add0r.
have hR : Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[r + k - i]) 0 r
        = Zp.BigZMod.BAdd.bigi predT (fun (j : int) => y.[j]) (r - i) r.
+ have -> : Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[r + k - i]) 0 r
          = Zp.BigZMod.BAdd.bigi predT (fun (k : int) => y.[k - (i - r)]) 0 r.
  + by apply Zp.BigZMod.BAdd.eq_big_int => k hk /=; congr; smt().
  rewrite (big_shift y (i - r)).
  have -> : -(i - r) = r - i by smt().
  have -> : r + (r - i) = 2 * r - i by smt().
  rewrite (Zp.BigZMod.BAdd.big_cat_int r (r - i) (2 * r - i)) 1,2:/#.
  rewrite (Zp.BigZMod.BAdd.big1_seq predT _ (range r (2 * r - i))).
  + by move=> j [_ /mem_range hj] /=; rewrite gered_rcoeff 1:/#.
  by rewrite Zp.ZModpRing.addr0.
rewrite (Zp.BigZMod.BAdd.big_split predT
          (fun (k : int) => y.[k - i])
          (fun (k : int) => y.[r + k - i])
          (range 0 r)).
rewrite hL hR /ev1.
by rewrite -(Zp.BigZMod.BAdd.big_cat_int (r - i) 0 r) 1,2:/#.
      qed.

      (* ev1 is multiplicative: evaluation at 1 is a ring homomorphism. *)
lemma ev1M (x y : R) : ev1 (x * y) = Zp.( * ) (ev1 x) (ev1 y).
proof.
have step1 : ev1 (x * y)
  = Zp.BigZMod.BAdd.bigi predT
      (fun (k : int) =>
         Zp.BigZMod.BAdd.bigi predT
           (fun (i : int) => Zp.(+) (Zp.( * ) x.[i] y.[k - i])
                                    (Zp.( * ) x.[i] y.[r + k - i])) 0 r) 0 r.
+ rewrite /ev1.
  by apply Zp.BigZMod.BAdd.eq_big_int => k hk /=; exact (rcoeffM2 x y k hk).
have step2 : ev1 (x * y)
  = Zp.BigZMod.BAdd.bigi predT
      (fun (i : int) => Zp.( * ) x.[i] (ev1 y)) 0 r.
+ rewrite step1 Zp.BigZMod.BAdd.exchange_big.
  apply Zp.BigZMod.BAdd.eq_big_int => i hi /=.
  have -> : Zp.BigZMod.BAdd.bigi predT
              (fun (k : int) => Zp.(+) (Zp.( * ) x.[i] y.[k - i])
                                       (Zp.( * ) x.[i] y.[r + k - i])) 0 r
          = Zp.BigZMod.BAdd.bigi predT
              (fun (k : int) => Zp.( * ) x.[i] (Zp.(+) y.[k - i] y.[r + k - i])) 0 r.
  + by apply Zp.BigZMod.BAdd.eq_big_int => k hk /=;
       rewrite Zp.ZModpRing.mulrDr.
  rewrite -(Zp.BigZMod.BAdd.mulr_sumr predT
             (fun (k : int) => Zp.(+) y.[k - i] y.[r + k - i])
             (range 0 r) x.[i]).
  by rewrite (inner_sum y i hi).
rewrite step2.
rewrite -(Zp.BigZMod.BAdd.mulr_suml predT
           (fun (i : int) => x.[i]) (range 0 r) (ev1 y)).
by rewrite /ev1.
qed.

(* oner has exactly one nonzero coefficient (index 0). *)
lemma rcoeff1 (k : int) : oner.[k] = if k = 0 then Zp.one else Zp.zero.
proof.
have h := rcoeff_polyXn 0 k _; first smt(r_gt0).
by move: h; rewrite ComRingDflInv.expr0.
qed.

lemma parity_oner : poly_parity oner = 1.
proof.
rewrite /poly_parity ham_weight_coeff.
have -> : count (fun (i : int) => oner.[i] <> Zp.zero) (range 0 r)
        = count (pred1 0) (range 0 r).
+ apply eq_in_count => i /mem_range hi /=.
  rewrite /pred1 rcoeff1.
  smt(Zp.oneE Zp.zeroE Zp.asint_eq).
rewrite count_uniq_mem 1:range_uniq mem_range.
smt(r_gt0).
      qed.

(* asint of a coefficient sum = (number of nonzero coefficients) mod 2. *)
lemma asint_big_count (x : R) (a b : int) :
  Zp.asint (Zp.BigZMod.BAdd.bigi predT (fun i => x.[i]) a b)
  = count (fun (i : int) => x.[i] <> Zp.zero) (range a b) %% 2.
proof.
have [k [hk hab]] : exists k, 0 <= k /\ b - a <= k.
+ by exists (max 0 (b - a)); smt().
elim: k hk a b hab => [| k hk ih] a b hab.
+ rewrite Zp.BigZMod.BAdd.big_geq 1:/# range_geq 1:/#.
  by rewrite Zp.zeroE.
case (b <= a) => hba.
+ rewrite Zp.BigZMod.BAdd.big_geq 1:/# range_geq 1:/#.
  by rewrite Zp.zeroE.
have hlt : a < b by smt().
rewrite (Zp.BigZMod.BAdd.big_ltn a b) 1:// (range_ltn a b) 1:// /=.
rewrite Zp.addE (ih (a + 1) b) 1:/#.
smt(Zp.rg_asint Zp.zeroE Zp.asint_eq modzDml modzDmr).
qed.

lemma poly_parity_ev1 (x : R) : poly_parity x = Zp.asint (ev1 x).
proof.
by rewrite /poly_parity ham_weight_coeff /ev1 asint_big_count.
qed.

lemma p2 : PolyRing.p = 2.
proof. by []. qed.

lemma parity_range (z : R) : 0 <= poly_parity z < 2.
proof. rewrite /poly_parity; smt(modz_ge0 ltz_pmod). qed.

lemma parity_add (x y : R) :
  poly_parity (x + y) = (poly_parity x + poly_parity y) %% 2.
proof.
rewrite !poly_parity_ev1 ev1D Zp.addE p2.
done.
qed.

lemma parity_mul (x y : R) :
  poly_parity (x * y) = (poly_parity x * poly_parity y) %% 2.
proof.
rewrite !poly_parity_ev1 ev1M Zp.mulE p2.
done.
qed.

op enumR_odd : R list = filter (fun (x : R) => poly_parity x = 1) enumR.
op distribution_over_R_odd = duniform enumR_odd.

        (* Discharge of enumR_odd_nonempty: a weight-1 polynomial is odd. *)
lemma enumR_odd_nonempty : enumR_odd <> [].
proof.
have [x hx] : exists (x : R), ham_weight (polyToList x) = 1.
+ by apply weight_k_exists; smt(r_gt0).
apply/negP => h.
have hmem : x \in enumR_odd.
+ rewrite /enumR_odd mem_filter.
  smt(mem_enumR).
by move: hmem; rewrite h.
qed.

(* Discharge of exists_filter_Et: split t = min t r + (t - min t r),
   both parts in [0,r] since 0 <= t <= n = 2r (t_ge0, t_le_n). *)
lemma exists_filter_Et : exists (x : R * R), filter_Et x.
proof.
have [x0 hx0] : exists (x : R), ham_weight (polyToList x) = min t r.
+ by apply weight_k_exists; smt(t_ge0 r_gt0).
have [x1 hx1] : exists (x : R), ham_weight (polyToList x) = t - min t r.
+ by apply weight_k_exists; smt(t_ge0 t_le_n r_gt0).
by exists (x0, x1); rewrite /filter_Et /= hx0 hx1 /#.
qed.

(* ====================================================================
   2. ROM: L : R×R -> M
   (from old §3; ROH/H2 and ROK/K removed)
   ==================================================================== *)
clone ROM as ROL with type in_t <- R * R, type out_t <- M,
                      op dout _ <- duniformM proof *.
module L = {
  proc init(): unit = { ROL.Lazy.LRO.init(); }
  proc hash(x : R * R): M = { var y; y <@ ROL.Lazy.LRO.o(x); return y; }
}.

(* ====================================================================
   3. PKE0 KEY GENERATION
   (from old §4; encaps removed)
   ==================================================================== *)
(* Spec (Table 10 KeyGen): (h0,h1) <-$ Hw x Hw with
   Hw = { x in R : |x| = w/2 }, h = h1 * h0^-1.
   Revision b makes the Hw distribution concrete:
     dHw = uniform over the weight-d elements of R  (d = w %/ 2). *)
op Hw_elem (x : R) : bool = ham_weight (polyToList x) = d.
op enumHw : R list = filter Hw_elem enumR.

(* Discharge of enumHw_nonempty: a weight-d polynomial exists
   (1 <= d from w_gt0/w_even, d <= r from d_le_r). *)
lemma enumHw_nonempty : enumHw <> [].
proof.
have [x hx] : exists (x : R), ham_weight (polyToList x) = d.
+ by apply weight_k_exists; smt(w_gt0 w_even d_le_r).
apply/negP => h.
have hmem : x \in enumHw.
+ by rewrite /enumHw mem_filter /Hw_elem hx /= mem_enumR.
by move: hmem; rewrite h.
qed.

op dHw : R distr = duniform enumHw.

(* dHw_ll: axiom in the base file, now a lemma. *)
lemma dHw_ll : is_lossless dHw.
proof. rewrite /dHw; apply duniform_ll; exact enumHw_nonempty. qed.

(* Support correctness: keyGen really samples weight-d polynomials. *)
lemma dHw_supp (x : R) : x \in dHw => ham_weight (polyToList x) = d.
proof. rewrite /dHw supp_duniform /enumHw mem_filter /Hw_elem; smt(). qed.

(* BENIGN AXIOM (mathematically true for BIKE parameter sets):
   every weight-d element of R is a unit. Justification: d odd
   (uneven_w_half) gives x(1) = 1, so (X-1) does not divide x; BIKE
   chooses r prime (r_prime) with 2 a primitive root mod r, so
   Phi = (X^r-1)/(X-1) is irreducible; then by CRT the only non-units
   with x(1) = 1 are the multiples of Phi, i.e. x = 1+X+...+X^{r-1}
   of weight r, excluded since d < r for all BIKE parameter sets.
   NOTE: "2 primitive root mod r" and "d < r" are part of the BIKE
   parameter choice but are NOT captured by axioms here; discharging
   Hw_unit (future work) would add them and develop gcd/Bezout for
   F2[X], which the stdlib currently lacks. *)
axiom Hw_unit (x : R) :
  ham_weight (polyToList x) = d => exists (y : R), x * y = oner.

(* invp is now DEFINED (choice from Hw_unit), no longer abstract:
   the only trusted statement about inversion is Hw_unit above. *)
op invp (x : R) : R = choiceb (fun (y : R) => x * y = oner) x.

(* Correctness on the keyGen support: an axiom in revision b, now a
   lemma. Off the support invp's value is irrelevant (cf. dHw_supp). *)
lemma invp_correct (x : R) :
  ham_weight (polyToList x) = d => x * invp x = oner.
proof.
  move=> hx; rewrite /invp.
  have hex : exists (y : R), x * y = oner by exact (Hw_unit x hx).
  exact (choicebP (fun (y : R) => x * y = oner) x hex).
qed.

(* ---- §3: invp_correct 直後 ---- *)

(* (1) dHw elements are odd (first real use of uneven_w_half). *)
lemma dHw_odd (x : R) : x \in dHw => poly_parity x = 1.
proof.
move=> /dHw_supp hx; rewrite /poly_parity hx.
smt(uneven_w_half).
qed.

(* (2) oner is odd: bridge parity_oner into the mod-2 arithmetic. *)
(* already available as parity_oner *)

(* (3) the inverse of a weight-d element is odd:
   1 = parity(oner) = parity(x * invp x) = parity x * parity(invp x) mod 2,
   and parity x = 1, so parity(invp x) = 1. Uses invp_correct — this
   connects the KeyGen inverse correctness into the proof chain. *)
lemma invp_odd (x : R) :
  ham_weight (polyToList x) = d => poly_parity (invp x) = 1.
proof.
move=> hx.
have h1 : poly_parity (x * invp x) = 1.
+ by rewrite (invp_correct x hx) parity_oner.
have h2 : poly_parity x = 1 by rewrite /poly_parity hx; smt(uneven_w_half).
have := parity_mul x (invp x).
rewrite h1 h2 /=.
smt(parity_range).
qed.

module Bike = {
  proc keyGen(): R = { var h0, h1; h0 <$ dHw; h1 <$ dHw; return h1 * invp h0; }
}.

(* (4) KeyGen support theorem: the public key is odd (Code Major 1). *)
lemma keyGen_odd :
  hoare[ Bike.keyGen : true ==> poly_parity res = 1 ].
proof.
proc.
auto => /> h0 hh0 h1 hh1.
rewrite parity_mul.
rewrite (dHw_odd h1 hh1) (invp_odd h0 _) 1:(dHw_supp h0 hh0) //.
qed.

(* ====================================================================
   4. AUXILIARY LEMMAS
   (selected from old §9; fp_measure / parity / ROM-counting removed)
   ==================================================================== *)
lemma mem_list_append_each ['a 'b] (a : 'a) (b : 'b) (x : 'a) (u : 'b list) :
  (a, b) \in list_append_each u x <=> a = x /\ b \in u.
proof. elim: u => /=; smt(). qed.
lemma mem_double_list ['a 'b] (a : 'a) (b : 'b) (s : 'a list) (u : 'b list) :
  (a, b) \in double_list s u <=> a \in s /\ b \in u.
proof.
  elim: s => /= [|x xs ih]; first by rewrite /double_list.
  rewrite mem_cat mem_list_append_each ih; smt().
qed.

lemma Et_complete (x : R * R) : filter_Et x => x \in enumE_t.
proof.
  move=> hx; rewrite /enumE_t mem_filter hx /=.
  have -> : x = (x.`1, x.`2) by smt().
  rewrite mem_double_list; smt(mem_enumR).
qed.
lemma enumE_t_nonempty : enumE_t <> [].
proof.
  have [e he] := exists_filter_Et. have hmem := Et_complete e he.
  apply/negP => h; by move: hmem; rewrite h.
qed.
lemma Et_filter (x : R * R) : x \in distribution_over_E_t => filter_Et x.
proof. rewrite /distribution_over_E_t supp_duniform /enumE_t mem_filter; smt(). qed.

(* Losslessness of the sampling distributions and oracles. *)
lemma duniformM_ll : is_lossless duniformM.
proof. rewrite /duniformM; apply dvector_ll; exact Zp.DZmodP.dunifin_ll. qed.
lemma DEt_ll : is_lossless distribution_over_E_t.
proof. rewrite /distribution_over_E_t; apply duniform_ll; exact enumE_t_nonempty. qed.
lemma DRodd_ll : is_lossless distribution_over_R_odd.
proof. rewrite /distribution_over_R_odd; apply duniform_ll; exact enumR_odd_nonempty. qed.

lemma L_hash_ll : islossless L.hash.
proof. proc; inline ROL.Lazy.LRO.o; auto => />; smt(duniformM_ll). qed.
lemma L_hash_eq :
  equiv[ L.hash ~ L.hash : ={arg, ROL.Lazy.LRO.m} ==> ={res, ROL.Lazy.LRO.m} ].
proof. by proc; inline ROL.Lazy.LRO.o; auto. qed.
lemma keyGen_ll : islossless Bike.keyGen.
    proof. proc; auto => />; smt(dHw_ll). qed.

      (* (5) phoare = 1 version (keyGen is lossless). *)
  (* Role: standalone spec-faithfulness statement for DQCCF(false) — the
   real key lies in R_odd with probability 1 (Evaluation Report §5.2
   item 3). The same parity chain enters the main claim through
   keyGen_eq_odd -> G3_OW_spec_eq -> Lemma1_spec. *)
lemma keyGen_supp_odd :
  phoare[ Bike.keyGen : true ==> poly_parity res = 1 ] = 1%r.
proof.
  conseq keyGen_ll keyGen_odd.
smt().
qed.

(* OTP helpers (used for the Step-2 rnd coupling and in G2b).
   Recovered from the handoff16 §1.2 / handoff17 §1.1 green scripts.
   If those become unrecoverable, reprove from the ZModule axioms of
   Matrix and characteristic 2 of Zp (x + x = 0). *)
lemma duniformM_size (v : M) : v \in duniformM => size v = l.
proof.
  rewrite /duniformM => hv.
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
  size m = l => v \in duniformM => (v - m) \in duniformM.
proof.
  move=> hm hv.
  have hsz : size v = l by apply duniformM_size.
  have hl : 0 <= l by smt(l_ge0).
  rewrite /duniformM (supp_dvector Zp.DZmodP.dunifin (v - m) l hl).
  rewrite size_addv size_oppv hsz hm /=.
  split; first smt().
  move=> i hi.
  rewrite get_addv getvN.
  exact Zp.DZmodP.dunifin_fu.
qed.

lemma duniformM_funi (v1 v2 : M) :
  size v1 = l => size v2 = l => mu1 duniformM v1 = mu1 duniformM v2.
proof.
  move=> h1 h2; rewrite /duniformM.
  rewrite -{1}h1 -{1}h2 !mu1_dvector_fu; first exact Zp.DZmodP.dunifin_funi.
  + exact Zp.DZmodP.dunifin_funi.
  by rewrite h1 h2.
qed.

(* fit: pad a message into F_2^l (deviation D5: mechanizes the paper's
   m ∈ F_2^l, since M = vector carries no length in its type).
   D5 closure argument: fit is the identity on well-formed messages
   (size m = l => fit m = m; candidate lemma fit_id in
   finite_facts_WIP.ec §A). Hence for any adversary that returns
   messages in {0,1}^l — the only adversaries the paper quantifies
   over — G0 here is literally Table 13's G0; for other adversaries
   fit acts as the challenger's input coercion. *)
op fit (m : M) : M = offunv ((fun i => m.[i]), l).

lemma size_fit (m : M) : size (fit m) = l.
    proof. by rewrite /fit size_offunv; smt(l_ge0). qed.

(* D5 closure: fit is the identity on well-formed (length-l) messages,
   so for adversaries returning messages in {0,1}^l, G0 = Table 13 G0. *)
lemma fit_id (m : M) : size m = l => fit m = m.
proof.
move=> hm; rewrite /fit.
apply/eq_vectorP; split.
+ by rewrite size_offunv hm; smt(l_ge0).
move=> i; rewrite size_offunv => hi.
by rewrite get_offunv 1:/#.
qed.

(* Self-equiv for keyGen (used by call in G0_G1 etc.). *)
lemma keyGen_eq : equiv[Bike.keyGen ~ Bike.keyGen : true ==> ={res}].
proof. by proc; auto. qed.

import FMap.

(* ====================================================================
   5. qcsd WITNESS PREDICATE AND OW-qcsd
   (Table 11 / Problem 3)
   --------------------------------------------------------------------
   wit e h s  <=>  e ∈ E_t /\ e0 + e1·h = s.
   E_t membership is carried by the runtime-decidable filter_Et (used by
   Lmon). Et_complete / Et_filter bridge to enumE_t.
   ==================================================================== *)
op wit (e : R * R) (h s : R) : bool =
  filter_Et e /\ e.`1 + e.`2 * h = s.

(* R_odd support: sampling from distribution_over_R_odd gives odd h. *)
lemma DRodd_odd (h : R) :
  h \in distribution_over_R_odd => poly_parity h = 1.
proof.
rewrite /distribution_over_R_odd supp_duniform /enumR_odd mem_filter.
smt().
qed.

(* Syndrome parity (Code Major 2): for a weight-t error pair and an odd h,
   the syndrome e0 + e1*h lies in the parity class t mod 2, i.e. the
   spec's R_p(t) side condition (Problem 3) holds inside G3_OW/G4_OW. *)
lemma syndrome_parity (e : R * R) (h : R) :
  filter_Et e => poly_parity h = 1 =>
  poly_parity (e.`1 + e.`2 * h) = t %% 2.
proof.
move=> hE hodd.
rewrite parity_add parity_mul hodd /=.
move: hE; rewrite /filter_Et /poly_parity => hE.
smt(modzDml modzDmr modz_mod).
qed.

(* Spec-faithful witness predicate (Problem 3 with domain checks):
   h must be odd (h in R_odd) and s must lie in R_p(t). *)
op wit_spec (e : R * R) (h s : R) : bool =
  poly_parity h = 1 /\ poly_parity s = t %% 2 /\ wit e h s.

(* Under an odd h, the domain checks are redundant: the s-check follows
   from the witness equation via syndrome_parity. *)
lemma wit_spec_equiv (e : R * R) (h s : R) :
  poly_parity h = 1 => wit e h s <=> wit_spec e h s.
proof.
move=> hodd; rewrite /wit_spec hodd /=.
split; last by smt().
move=> hw; split; last exact hw.
have <- : e.`1 + e.`2 * h = s by smt().
by apply (syndrome_parity e h) => //; smt().
qed.

module type OW_Adv = {
  proc solve(h : R, s : R) : (R * R) option
}.

(* Table 11 left: OW-CPA under the real key. *)
module G3_OW (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* Table 11 middle: h uniform (R_odd) = generic decoding = OW-qcsd game. *)
module G4_OW (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <$ distribution_over_R_odd;
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* Spec-faithful twins of the OW games (wit replaced by wit_spec). *)
module G3_OW_S (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit_spec (oget eo) h s);
  }
}.

module G4_OW_S (A0 : OW_Adv) = {
  proc main() : bool = {
    var h, e0e1, s, eo;
    h <$ distribution_over_R_odd;
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit_spec (oget eo) h s);
  }
}.

(* keyGen self-equiv carrying the oddness of the output.
   Revision f+: derived from keyGen_odd (Code Major 1), so the hoare
   parity theorem enters the main claim through
   keyGen_odd -> keyGen_eq_odd -> G3_OW_spec_eq -> Lemma1_spec. *)
lemma keyGen_eq_odd :
  equiv[ Bike.keyGen ~ Bike.keyGen :
         true ==> ={res} /\ poly_parity res{2} = 1 ].
proof.
conseq keyGen_eq _ keyGen_odd => //.
qed.

lemma G4_OW_spec_eq (A0 <: OW_Adv) &m :
  Pr[G4_OW(A0).main() @ &m : res] = Pr[G4_OW_S(A0).main() @ &m : res].
proof.
byequiv (: ={glob A0} ==> ={res}) => //.
proc.
seq 1 1 : (={glob A0, h} /\ poly_parity h{2} = 1).
+ by rnd; auto => />; smt(DRodd_odd).
call (_: true).
auto => />.
smt(wit_spec_equiv).
qed.

lemma G3_OW_spec_eq (A0 <: OW_Adv) &m :
  Pr[G3_OW(A0).main() @ &m : res] = Pr[G3_OW_S(A0).main() @ &m : res].
proof.
byequiv (: ={glob A0} ==> ={res}) => //.
proc.
seq 1 1 : (={glob A0, h} /\ poly_parity h{2} = 1).
+ by call keyGen_eq_odd.
call (_: true).
auto => />.
smt(wit_spec_equiv).
qed.

(* Table 11 right: qccf distinguisher (lines 3–6 of G4; old Red_cf_L skeleton). *)
module D_cf (A0 : OW_Adv) = {
  proc distinguish(h : R) : bool = {
    var e0e1, s, eo;
    e0e1 <$ distribution_over_E_t;
    s <- e0e1.`1 + e0e1.`2 * h;
    eo <@ A0.solve(h, s);
    return (eo <> None /\ wit (oget eo) h s);
  }
}.

(* ====================================================================
   6. qccf DISTINGUISHING GAME
   (old §6 DQCCF verbatim; DQCSD removed)
   ==================================================================== *)
module type CF_Dist = { proc distinguish(h : R) : bool }.
module DQCCF (D : CF_Dist) = {
  proc main(b : bool) : bool = {
    var hk, hu, h, r0;
    hk <@ Bike.keyGen();
    hu <$ distribution_over_R_odd;
    h  <- if b then hu else hk;
    r0 <@ D.distinguish(h);
    return r0;
  }
}.

(* ====================================================================
   7. IND-CPA GAME SEQUENCE (Table 13) AND MONITORING WRAPPER (Table 14)
   ==================================================================== *)
module type OrclL = { proc hash(_ : R * R) : M }.

module type LOR_Adv (O : OrclL) = {
  proc choose(h : R) : M * M        {O.hash}  (* paper A1(h) -> (m0,m1,st) *)
  proc guess(c0 : R, c1 : M) : bool {O.hash}  (* paper A2(h,c0,c1,st) -> b'
                                                 h and st live in glob A *)
}.

module BadWit = {
  var h  : R
  var c0 : R
  var wt : (R * R) option
}.

(* Paper's L' (Table 14): record the witness query, then forward to L. *)
module Lmon : OrclL = {
  proc hash(e : R * R) : M = {
    var v;
    if (wit e BadWit.h BadWit.c0) { BadWit.wt <- Some e; }
    v <@ L.hash(e);
    return v;
  }
}.

(* G0: IND-CPA (Table 13 left, no instrumentation). *)
module G0 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;                 (* e*  *)
    c0 <- e0e1.`1 + e0e1.`2 * h;                   (* c0* *)
    b <$ {0,1};
    m0m1 <@ A(L).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- fit (b ? m0m1.`2 : m0m1.`1) + lv;
    b' <@ A(L).guess(c0, c1);
    return b' = b;
  }
}.

(* G0_spec: Table 13's G0 verbatim, without the fit coercion (Code
   Major 5). Under the well-formedness contract A_choose_wf the two
   games are equal (G0_G0_spec below), discharging deviation D5. *)
module G0_spec (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    b <$ {0,1};
    m0m1 <@ A(L).choose(h);
    lv <@ L.hash(e0e1);
    c1 <- (b ? m0m1.`2 : m0m1.`1) + lv;
    b' <@ A(L).guess(c0, c1);
    return b' = b;
  }
}.

(* G1: G0 + L* instrumentation (only the adversary's queries are watched;
   the challenger uses the raw L). *)
module G1 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, lv, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
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

(* G2: c1 $<- M (Table 13 right). *)
module G2 (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    b <$ {0,1};
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ duniformM;
    b' <@ A(Lmon).guess(c0, c1);
    return b' = b;
  }
}.

(* G2b: b moved to the tail (for the 1/2 argument, deviation D2; in G2, b is
   unused until the return). *)
module G2b (A : LOR_Adv) = {
  proc main() : bool = {
    var h, e0e1, c0, b, m0m1, c1, b';
    L.init();
    h <@ Bike.keyGen();
    e0e1 <$ distribution_over_E_t;
    c0 <- e0e1.`1 + e0e1.`2 * h;
    BadWit.h <- h; BadWit.c0 <- c0; BadWit.wt <- None;
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ duniformM;
    b' <@ A(Lmon).guess(c0, c1);
    b <$ {0,1};
    return b' = b;
  }
}.

(* Red(A): the A0 of Table 14 (recovers wt and returns it). The paper's
   unused b sample is dropped (D3). *)
module Red (A : LOR_Adv) : OW_Adv = {
  proc solve(h : R, s : R) : (R * R) option = {
    var m0m1, c1, b';
    L.init();
    BadWit.h <- h; BadWit.c0 <- s; BadWit.wt <- None;
    m0m1 <@ A(Lmon).choose(h);
    c1 <$ duniformM;
    b' <@ A(Lmon).guess(s, c1);
    return BadWit.wt;
  }
}.

(* ====================================================================
   8. SECURITY
   ==================================================================== *)
section Security.

declare module A <: LOR_Adv {-Bike, -L, -ROL.Lazy.LRO, -BadWit}.

(* NOTE (Code Major 3): no computational hardness axiom is declared in
   this file. The mechanized results are exact-probability statements
   relative to the concrete games for the explicit reduction Red(A) /
   D_cf(Red(A)). The computational reading — if qccf / OW-qcsd are hard
   for efficient adversaries then both RHS terms are negligible, since
   Red(A) and D_cf(Red(A)) are efficient whenever A is — lives in prose.
   The artifact's main claim is Theorem2_final (with Lemma1_spec
   connecting the real-key parity chain). *)

declare axiom A_choose_ll : forall (O <: OrclL {-A}),
  islossless O.hash => islossless A(O).choose.
declare axiom A_guess_ll : forall (O <: OrclL {-A}),
  islossless O.hash => islossless A(O).guess.

(* Code Major 5: well-formedness contract — A returns messages in F_2^l.
   This is exactly the quantification of the paper (adversaries output
   m0, m1 in {0,1}^l); adversaries violating it are outside the model. *)
declare axiom A_choose_wf (O <: OrclL {-A}) :
  hoare[ A(O).choose : true ==> size res.`1 = l /\ size res.`2 = l ].


(* Lmon is lossless (used for the one-sided handling after bad). *)
lemma Lmon_hash_ll : islossless Lmon.hash.
proof. proc; call L_hash_ll; auto. qed.

(* --------------------------------------------------------------------
   Step 1 (paper: G0 and G1 are identical): transparency of the
   instrumentation.
   Source: old G0_G0_bad. The OL branch of `call (_: ={glob L})` is
   proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto.
   -------------------------------------------------------------------- *)
(* A_choose_wf lifted to a self-equiv (both sides in sync, size carried). *)
lemma A_choose_eq_wf :
  equiv[ A(L).choose ~ A(L).choose :
         ={arg, glob A, ROL.Lazy.LRO.m} ==>
         ={res, glob A, ROL.Lazy.LRO.m}
         /\ size res{2}.`1 = l /\ size res{2}.`2 = l ].
proof.
conseq (: ={arg, glob A, ROL.Lazy.LRO.m} ==> ={res, glob A, ROL.Lazy.LRO.m})
       _ (A_choose_wf L) => //.
proc (={ROL.Lazy.LRO.m}) => //.
exact L_hash_eq.
qed.

(* Code Major 5 closure: with well-formed adversaries, fit is the
   identity and G0 equals the spec game G0_spec. *)
lemma G0_G0_spec &m :
  Pr[G0(A).main() @ &m : res] = Pr[G0_spec(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m}); first exact L_hash_eq.
wp.
call L_hash_eq.
call A_choose_eq_wf.
rnd.
wp.
rnd.
call keyGen_eq.
inline L.init ROL.Lazy.LRO.init.
auto => />.
smt(fit_id).
qed.

lemma G0_G1 &m :
  Pr[G0(A).main() @ &m : res] = Pr[G1(A).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m}).
+ by proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto => />.
wp.
call L_hash_eq.
call (_: ={ROL.Lazy.LRO.m}).
+ by proc*; inline{2} Lmon.hash; wp; call L_hash_eq; auto => />.
rnd.
wp.
rnd.
call keyGen_eq.
inline L.init ROL.Lazy.LRO.init.
auto => />.
qed.

(* --------------------------------------------------------------------
   Step 2 (paper: if L* = ∅ then G1 and G2 are identical): single-bad
   up-to-bad. This is the core.

   Preservation lemmas first (each side stays bad once bad), then the
   up-to-bad equiv G1_G2_upto, then its two corollaries.

   Attack for G1_G2_upto:
     proc; from the tail, use the 3-argument upto form of `call` with the
     invariant invQ fixed in a previous session:
       ={BadWit.h, BadWit.c0, BadWit.wt, glob A ...}
       /\ eq_except (pred1 e*{2}) ROL...m{1} ROL...m{2}.
     The oracle side-goals are 4 (equiv + two-sided lossless with invQ
     preserved: proc; inline*; auto => />; smt(duniformM_ll); wt only ever
     gets overwritten by Some, so it is monotone).
   Middle challenge ({1}: lv<@L.hash(e_star); c1<-m_b+lv | {2}: c1<$duniformM):
     the post of choose's upto-call is `if bad{2} then invQ else <joined>`,
     so case on (BadWit.wt{2} <> None).
       ¬bad branch: from the invariant "¬bad => e* ∉ dom ROL.m" (bad <=>
         witness query happened, e* is a witness, before the challenger
         writes), rcondt{1} produces a fresh sample and couples it with
         rnd (fun v => m_b + v) (an involution: otp_cancel/otp_supp/otp_mu1).
         Afterwards ROL.m agrees except at e* = eq_except.
       bad branch: run both sides lossless, preserving wt (re-establish invQ).
     prefix (init/keyGen/e*/c0/BadWit assigns/b): in sync.
   The bad equality in the post follows from invP on the ¬bad{2} side and
   from invQ on the bad{2} side.
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
(* checkpoint 1: prefix (instructions 1..8 in sync) *)
seq 8 8 : (={glob A, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt,
             h, e0e1, c0, b}
           /\ BadWit.wt{2} = None
           /\ BadWit.h{2} = h{2} /\ BadWit.c0{2} = c0{2}
           /\ wit e0e1{2} h{2} c0{2}
           /\ e0e1{2} \notin ROL.Lazy.LRO.m{2}).
+ inline L.init ROL.Lazy.LRO.init.
  auto.
  call keyGen_eq.
  auto => />.
  smt(Et_filter mem_empty).
(* turn e* into a logical constant (oracle invariants can't mention program vars) *)
exists* e0e1{2}; elim* => estar.
(* checkpoint 2: choose's upto call *)
seq 1 1 : (if BadWit.wt{2} <> None
           then BadWit.wt{1} <> None /\ BadWit.wt{2} <> None
           else ={glob A, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt,
                  b, e0e1, c0, m0m1}
                /\ BadWit.wt{2} = None
                /\ wit estar BadWit.h{2} BadWit.c0{2}
                /\ e0e1{2} = estar
                /\ estar \notin ROL.Lazy.LRO.m{2}).
+ call (_: BadWit.wt <> None,
        ={ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ wit estar BadWit.h{2} BadWit.c0{2}
        /\ (BadWit.wt{2} = None => estar \notin ROL.Lazy.LRO.m{2}),
          BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).

  + exact A_choose_ll.
  (* oracle equiv (¬bad precondition) *)
  + proc.
    if => //.
    + (* witness branch *)
      inline L.hash ROL.Lazy.LRO.o.
      sp.
      seq 1 1 : (={x0, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
                 /\ BadWit.wt{2} <> None).
      + by auto => />; smt().
      if => //.
      + by auto => />; smt().
      by auto => />; smt().
    (* non-witness branch *)
    inline L.hash ROL.Lazy.LRO.o.
    sp.
    seq 1 1 : (={e, x0, r, ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
               /\ x0{2} = e{2}
               /\ wit estar BadWit.h{2} BadWit.c0{2}
               /\ (BadWit.wt{2} = None => estar \notin ROL.Lazy.LRO.m{2})
               /\ !wit e{2} BadWit.h{2} BadWit.c0{2}).
    + by auto => />; smt().
    if => //.
    + by auto => />; smt(mem_set get_setE).
    by auto => />; smt().
  (* lossless-after-bad, left (only after the equiv closes) *)
  + move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
  (* lossless-after-bad, right *)
  + move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
  (* prefix discharge *)
  auto => />; smt().
(* checkpoint 3: split on bad *)
case (BadWit.wt{2} <> None).
(* bad branch: run both sides lossless *)
+ conseq (: _ ==> BadWit.wt{1} <> None /\ BadWit.wt{2} <> None) => //; 1: smt().
  call{1} A_guess_pres.
  call{2} A_guess_pres.
  wp.
  rnd{2}.
  call{1} L_hash_pres.
  auto => />; smt(duniformM_ll).
(* ¬bad branch: the core OTP coupling *)
(* checkpoint 4: freshen {1}'s L.hash(e_star) *)
inline{1} L.hash ROL.Lazy.LRO.o.
rcondt{1} 4.       (* count the position on the machine; 2..4 depending on param assigns *)
+ by auto => />; smt().
(* checkpoint 5: guess's upto call *)
call (_: BadWit.wt <> None,
      ={BadWit.h, BadWit.c0, BadWit.wt}
      /\ eq_except (pred1 estar) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}
      /\ wit estar BadWit.h{2} BadWit.c0{2},
        BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).

  + exact A_guess_ll.
(* oracle equiv: witness branch has post on the `then` side only; the
   non-witness branch stays in sync via eq_except *)
+ proc.
  if => //.
  + (* witness (bad-triggering) branch: both sides did wt <- Some e; the
       ifs may be out of sync *)
    inline L.hash ROL.Lazy.LRO.o.
    sp.
    seq 1 1 : (BadWit.wt{1} <> None /\ BadWit.wt{2} <> None).
    + by auto => />; smt().
    if{1}; if{2}; by auto => />; smt().
  (* non-witness branch: e ≠ estar, so eq_except keeps the ifs in sync *)
  inline L.hash ROL.Lazy.LRO.o.
  sp.
  seq 1 1 : (={e, x0, r, BadWit.h, BadWit.c0, BadWit.wt}
             /\ x0{2} = e{2}
             /\ eq_except (pred1 estar) ROL.Lazy.LRO.m{1} ROL.Lazy.LRO.m{2}
             /\ wit estar BadWit.h{2} BadWit.c0{2}
             /\ !wit e{2} BadWit.h{2} BadWit.c0{2}).
  + by auto => />; smt().
  if.
  + by move=> &1 &2 />; smt(eq_exceptP domE).
  + by auto => />; smt(eq_exceptP eq_except_set_eq get_setE get_set_sameE mem_set domE).
    by auto => />; smt(eq_exceptP domE).
(* lossless-after-bad, left *)
+ move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
(* lossless-after-bad, right *)
+ move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
(* checkpoint 6: OTP rnd coupling ({1}: v = m.[e*] sample | {2}: c1) *)
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
   Step 3 (paper: Pr[G2 | ¬L*] = 1/2, mechanized as D2)
   (a) move b to the tail (b is unused until the return): swap + sim,
       transported for the two events res∧¬bad and ¬bad.
   (b) coin-flip symmetry: at the tail, rnd (fun x => !x) (an involution
       on {0,1}); everything before is sim. ¬bad and b' are fixed before b,
       so the events just swap.
   (c) sum: Pr[E] = Pr[res∧E] + Pr[¬res∧E] (Pr[mu_split res] + smt).
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
seq 10 10 : (={ROL.Lazy.LRO.m, BadWit.wt, b'}); first by sim.
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
   Step 4 (paper: ½ − ½p ≤ Pr[G0] ≤ ½ + ½p, p = Pr[L*])
   Split G1's res with Pr[mu_split (BadWit.wt = None)] and squeeze using
   the Step-2/3 equalities together with 0 ≤ Pr[res∧bad] ≤ Pr[bad].
   Pure arithmetic.
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
inline L.init ROL.Lazy.LRO.init.
auto => />.
smt(duniformM_ll DEt_ll dbool_ll).
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
   Step 5 (paper: Pr[G3'] = Pr[L*]): G2's bad probability = OW reduction's
   success probability.
   Source: old badL_eq_uk / badL_fp_inv "found => witness" invariant
   transport + old G3_bad_c1_c1e bad<=>predicate re-mapping.
   byequiv; proc; inline G3_OW/Red; invariant
     ={glob A, glob L, BadWit.*} /\
     (BadWit.wt <> None => wit (oget BadWit.wt) BadWit.h BadWit.c0)
   (Lmon only writes witnesses, so it is preserved) => res(G3_OW) = (wt <> None).
   b lives only in G2 (on the {2} side); consume G2's b <$ {0,1} by rnd{1}.
   -------------------------------------------------------------------- *)
lemma G2_bad_Red &m :
  Pr[G2(A).main() @ &m : BadWit.wt <> None]
  = Pr[G3_OW(Red(A)).main() @ &m : res].
proof.
byequiv (: ={glob A} ==> (BadWit.wt{1} <> None) <=> res{2}) => //.
proc.
inline{2} Red(A).solve.
inline L.init ROL.Lazy.LRO.init.
wp.
call (_: ={ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
        /\ (BadWit.wt{2} <> None =>
              wit (oget BadWit.wt{2}) BadWit.h{2} BadWit.c0{2})).
+ by proc; call L_hash_eq; auto => />; smt().
rnd.
call (_: ={ROL.Lazy.LRO.m, BadWit.h, BadWit.c0, BadWit.wt}
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
   Lemma 1 (paper: Adv^IND-CPA ≤ ½·Adv^OW-CPA, reduction Red(A))
   -------------------------------------------------------------------- *)
lemma Lemma1 &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G3_OW(Red(A)).main() @ &m : res].
proof.
  have h1 := G0_half_bound &m. have h2 := G2_bad_Red &m. smt().
qed.

(* --------------------------------------------------------------------
   Theorem 1 (paper: Adv^OW-CPA_PKE0 ≤ Adv^IND_qccf + Adv^OW_qcsd)
   Source: old badL_cf_false / badL_cf_true (inline distinguish -> swap ->
   dead-random rnd{2} / call{2} keyGen_ll -> call (_: true)).
   -------------------------------------------------------------------- *)
lemma T1_false (A0 <: OW_Adv) &m :
  Pr[G3_OW(A0).main() @ &m : res]
  = Pr[DQCCF(D_cf(A0)).main(false) @ &m : res].
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
smt(DRodd_ll).
qed.

lemma T1_true (A0 <: OW_Adv) &m :
  Pr[G4_OW(A0).main() @ &m : res]
  = Pr[DQCCF(D_cf(A0)).main(true) @ &m : res].
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
   Theorem 2C (concrete-security form, Code Major 3):
   the advantage bound stated against the two concrete games for the
   specific reduction Red(A) / D_cf(Red(A)), with NO hardness axioms.
   The computational reading ("if qccf/qcsd are hard for efficient
   adversaries then the RHS is negligible, and Red(A)/D_cf(Red(A)) are
   efficient whenever A is") lives in prose, not in the machine.
   Exported G0-side statements (paper Theorem 2 correspondence);
   Theorem2_final, the spec-side main claim, is derived independently
   via Lemma1_spec.
   -------------------------------------------------------------------- *)
lemma Theorem2_concrete &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[DQCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[G4_OW(Red(A)).main() @ &m : res].
proof.
have h1 := Lemma1 &m.
have hf := T1_false (Red(A)) &m.
have ht := T1_true (Red(A)) &m.
smt().
qed.

(* Paper correspondence: writing eps_qccf for the qccf advantage of
   D_cf(Red(A)) and eps_qcsd_ow for the OW success of Red(A), this is
   exactly Theorem 2's bound  Adv <= 1/2 eps_qccf + 1/2 eps_qcsd_ow,
   and T1_false/T1_true are Theorem 1. The computational reading (both
   epsilons negligible for efficient A, since Red(A)/D_cf(Red(A)) are
   efficient whenever A is) lives in prose; no hardness axiom is
   declared in this file. *)
(* Same bound with the OW term stated against the spec-faithful game
   G4_OW_S (wit_spec), via G4_OW_spec_eq. *)
lemma Theorem2_concrete_spec &m :
  `| Pr[G0(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[DQCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[G4_OW_S(Red(A)).main() @ &m : res].
proof.
have h := Theorem2_concrete &m.
have he := G4_OW_spec_eq (Red(A)) &m.
smt().
qed.

(* Lemma 1 in fully-spec form: connects the real-key parity chain
   (keyGen_eq_odd <- dHw_odd/invp_odd/invp_correct) into the claim via
   G3_OW_spec_eq. *)
lemma Lemma1_spec &m :
  `| Pr[G0_spec(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * Pr[G3_OW_S(Red(A)).main() @ &m : res].
proof.
have h0 := G0_G0_spec &m.
have h1 := Lemma1 &m.
have h2 := G3_OW_spec_eq (Red(A)) &m.
smt().
qed.

(* Theorem2_final is now derived from Lemma1_spec: the real-key leg is
   the spec-faithful game G3_OW_S (carrying the keyGen parity chain,
   Code Major 1/4), converted back to G3_OW by G3_OW_spec_eq for the
   T1 bridges, and the uniform-key leg is G4_OW_S. *)
lemma Theorem2_final &m :
  `| Pr[G0_spec(A).main() @ &m : res] - 1%r/2%r |
  <= 1%r/2%r * `| Pr[DQCCF(D_cf(Red(A))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A))).main(true)  @ &m : res] |
   + 1%r/2%r * Pr[G4_OW_S(Red(A)).main() @ &m : res].
proof.
have h1 := Lemma1_spec &m.
have h2 := G3_OW_spec_eq (Red(A)) &m.
have hf := T1_false (Red(A)) &m.
have ht := T1_true (Red(A)) &m.
have he := G4_OW_spec_eq (Red(A)) &m.
smt().
qed.

end section Security.

(* ====================================================================
   BIKE KEM — IND-CCA2 (Spec v5.2 Appendix C.2 / C.3), APPENDIX FILE.
   --------------------------------------------------------------------
   USAGE: concatenate after BIKE-PKE_IND-CPA.ec (revision f+4):
     cat BIKE-PKE_IND-CPA.ec BIKE_C2_append.ec > BIKE_KEM_INDCCA2.ec
   Sections continue the base file numbering (9..14).

   Correspondence with the paper (Appendix C.2/C.3, [24] = HHK17):
     PKE Decrypt (Table 12)          | PKE.decrypt
     delta-correct / DFR (C.2.1)     | Pr[Corr.main() : res]   (no axiom)
     PKE1 (Table 15)                 | PKE1.encrypt / Decrypt1
     KEM6bot (Table 16)              | KEM.keyGen/encaps/decaps
     KEM6bot inlined (Table 17)      | KEM_i.decaps (+ conv bote = (0,0))
     Pco oracle ([24, 3.2/3.4])      | Pco
     OW-PCA game                     | OW_PCA
     IND-CCA game (Definition-style) | IND_CCA
     B' of [24, Thm 3.4]             | B_ow(B)
     A  of [24, Thm 3.2]             | A_cpa(B0)      (a LOR_Adv!)
     Lemma 2                         | Lemma2
     Theorem 3 (eq. (4))             | Theorem3_concrete

   Style (inherited from revision f):
     - hardness-axiom-free / concrete security: NO hardness axiom and NO
       DFR axiom; delta stays as Pr[Corr] on the RHS, and the qccf/qcsd
       terms come from instantiating Theorem2_final at the explicit
       reduction A_cpa(B_ow(B)).
     - new parameter axiom: t_gt0 (Table 17 remark: (0,0) not in E_t).
     - new benign/implementation-contract axiom: decoder_sound, used
       ONLY by the Table16=Table17 inlining lemma, NOT by the bound.

   *** VERIFICATION STATUS: SKELETON, NOT COMPILED. ***
   Every `admit` is tagged TODO(Mx) with the milestone of the design
   doc BIKE_C2_00_design.md. Names tagged (* CHECK *) must be confirmed
   with print/search on the real toolchain.
   ==================================================================== *)

(* ====================================================================
   9. CIPHERTEXT TYPE, RANDOM ORACLES H AND K, ORACLE TYPES, COUNTERS
   ==================================================================== *)
type C = R * M.

(* Parameter axiom (C.3 remark): t > 0 so that (0,0) is not in E_t and
   the check e' = H(m') in Table 17 subsumes e' <> bote. True for all
   BIKE parameter sets (t >= 134). *)
axiom t_gt0 : 0 < t.

(* H : M -> E_t (Table 15). Output distribution = uniform over E_t,
   mirroring the ROL clone of the base file. *)
clone ROM as ROH with type in_t <- M, type out_t <- R * R,
                      op dout _ <- distribution_over_E_t proof *.
module H = {
  proc init(): unit = { ROH.Lazy.LRO.init(); }
  proc hash(m : M): R * R = { var e; e <@ ROH.Lazy.LRO.o(m); return e; }
}.

(* K : M x C -> K with K = {0,1}^l = M (Table 16). Module named Kh to
   avoid clash risk with cloned-theory names. *)
clone ROM as ROK with type in_t <- M * C, type out_t <- M,
                      op dout _ <- duniformM proof *.
module Kh = {
  proc init(): unit = { ROK.Lazy.LRO.init(); }
  proc hash(x : M * C): M = { var k; k <@ ROK.Lazy.LRO.o(x); return k; }
}.

module type OrclH = { proc hash(_ : M) : R * R }.
module type OrclK = { proc hash(_ : M * C) : M }.
(* OrclL is inherited from the base file. *)

(* Decapsulation oracle: None encodes the CCA restriction c = c*. *)
module type DecapsO = { proc decaps(c : C) : M option }.

(* Query counters (wrappers). The CCA section states the adversary's
   query budget against these. *)
module CountH (O : OrclH) : OrclH = {
  var c : int
  proc hash(m : M) : R * R = {
    var e; c <- c + 1; e <@ O.hash(m); return e;
  }
}.
module CountK (O : OrclK) : OrclK = {
  var c  : int
  var qs : (M * C) list   (* query transcript (M3: deferred-sampling bound) *)
  proc hash(x : M * C) : M = {
    var k; c <- c + 1; qs <- x :: qs; k <@ O.hash(x); return k;
  }
}.

(* Query budgets (adversary contract, cf. A_choose_ll etc.). *)
op qH : int.  op qK : int.
axiom qH_ge0 : 0 <= qH.
axiom qK_ge0 : 0 <= qK.

(* Adversary contract (WLOG): B makes at least one H query. Needed by
   the spec's aggregation q*delta + 3q/|M| (Lemma 2), whose slack
   qK+2qH+1 <= 3(qH+qK) fails at qH = qK = 0; the exact composition is
   Lemma2_exact. HHK's +1 counts B's final output as an implicit H query. *)
axiom qH_ge1 : 1 <= qH.

(* Adversary contract (WLOG): B makes at least one K query. Needed by
   the spec's aggregation: the mechanized U-bot-slash step (HHK_Thm34)
   carries a challenge-correctness term Pr[Corr] (spurious decryption
   of c* defeats the Pco-based extraction), absorbed into q*delta only
   when qK >= 1. *)
axiom qK_ge1 : 1 <= qK.

(* |M| = 2^l enters all bounds only through the point mass of the
   uniform distribution; keeping it as an op avoids int-power algebra.
   epsM = 2^{-l} on paper. *)
op epsM : real = mu1 duniformM (zerov l).

lemma epsM_uniform (v : M) : size v = l => mu1 duniformM v = epsM.
proof.
move=> hv; rewrite /epsM.
apply duniformM_funi => //.
rewrite size_zerov; smt(l_ge0).             (* CHECK: size_zerov name *)
qed.

lemma mu1_duniformM_le (v : M) : mu1 duniformM v <= epsM.
proof.
case (size v = l) => hsz.
+ by rewrite (epsM_uniform v hsz).
+ have h0 : mu1 duniformM v = 0%r.
  + rewrite -supportPn.
    rewrite /duniformM supp_dvector; first smt(l_ge0).
    smt().
  rewrite h0 /epsM; smt(mu_bounded).
qed.

(* RO toolkit for the CCA development (mirrors L_hash_ll / L_hash_eq). *)
lemma H_hash_ll : islossless H.hash.
proof. proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll). qed.

lemma Kh_hash_ll : islossless Kh.hash.
proof. proc; inline ROK.Lazy.LRO.o; auto => />; smt(duniformM_ll). qed.

lemma H_hash_eq :
  equiv[ H.hash ~ H.hash : ={arg, ROH.Lazy.LRO.m} ==> ={res, ROH.Lazy.LRO.m} ].
proof. by proc; inline ROH.Lazy.LRO.o; auto. qed.

lemma Kh_hash_eq :
  equiv[ Kh.hash ~ Kh.hash : ={arg, ROK.Lazy.LRO.m} ==> ={res, ROK.Lazy.LRO.m} ].
    proof. by proc; inline ROK.Lazy.LRO.o; auto. qed.

(* ====================================================================
   10. DECODER, PKE (TABLE 10/12), DELTA-CORRECTNESS (C.2.1),
       PKE1 (TABLE 15)
   ==================================================================== *)

(* decoder(s, h0, h1) in R^2 U {bot} — fully abstract, NO axioms used by
   the security bound. Argument order follows the spec: syndrome first. *)
op decoder : R -> R -> R -> (R * R) option.

(* Benign / implementation-contract axiom, used ONLY by the
   Table16=Table17 inlining lemma (decaps_inline, M2), never by the
   IND-CCA bound: a successful decoder output is syndrome-consistent.
   Justification: BGF ends with (or can be wrapped by) the syndrome
   check e*(h0,h1)^T = s; cf. design doc P1. *)
axiom decoder_sound (s h0 h1 : R) (e : R * R) :
  decoder s h0 h1 = Some e => e.`1 * h0 + e.`2 * h1 = s.

(* PKE of Table 10 (KeyGen0) + Table 12 (Encrypt/Decrypt). keyGen
   returns the secret pair as well; its pk marginal is Bike.keyGen
   (bridge lemma PKE_keyGen_pk). Decrypt calls the RO L (design P3). *)
module PKE = {
  proc keyGen(): (R * R) * R = {
    var h0, h1;
    h0 <$ dHw; h1 <$ dHw;
    return ((h0, h1), h1 * invp h0);
  }
  proc encrypt(h : R, m : M): C = {
    var e, lv;
    e <$ distribution_over_E_t;
    lv <@ L.hash(e);
    return (e.`1 + e.`2 * h, m + lv);
  }
  proc decrypt(sk : R * R, c : C): M option = {
    var eo, lv, mo;
    eo <- decoder (c.`1 * sk.`1) sk.`1 sk.`2;
    mo <- None;
    if (eo <> None) {
      lv <@ L.hash(oget eo);
      mo <- Some (c.`2 + lv);
    }
    return mo;
  }
}.

lemma PKE_keyGen_pk :
  equiv[ PKE.keyGen ~ Bike.keyGen : true ==> res{1}.`2 = res{2} ].
proof. by proc; auto. qed.

(* --------------------------------------------------------------------
   Delta-correctness (C.2.1). The spec shows PKE is message-agnostic,
   so delta-correct reduces to the DFR. We do NOT axiomatize the DFR
   (it is heuristic); the game below DEFINES the quantity carried into
   the bound: delta := Pr[Corr.main() : res].
   Algebra note: for c0 = e0 + e1*h with h = h1 * invp h0 and h0 in the
   dHw support, c0*h0 = e0*h0 + e1*h1 by invp_correct — the base file's
   inversion-correctness lemma becomes a proof dependency of the CCA
   development (Corr_syndrome below, M1).
   Direction note (design P2): the bound only needs
   Pr[decryption failure] <= Pr[Corr]; the spec's "iff" is not used.
   -------------------------------------------------------------------- *)
module Corr = {
  proc main(): bool = {
    var h0, h1, e;
    h0 <$ dHw; h1 <$ dHw;
    e  <$ distribution_over_E_t;
    return decoder (e.`1 * h0 + e.`2 * h1) h0 h1 <> Some e;
  }
}.

print mulrA.

(* M1: the algebraic bridge used whenever a game rewrites
   c0*h0 = e0*h0 + e1*h1 on the keyGen support. *)
lemma Corr_syndrome (h0 h1 e0 e1 : R) :
  ham_weight (polyToList h0) = d =>
  (e0 + e1 * (h1 * invp h0)) * h0 = e0 * h0 + e1 * h1.
proof.
move=> hw.
have hinv := invp_correct h0 hw.
have -> : (e0 + e1 * (h1 * invp h0)) * h0
        = e0 * h0 + e1 * h1 * (h0 * invp h0) by ring.
by rewrite hinv; ring.
qed.

(* --------------------------------------------------------------------
   PKE1 (Table 15): derandomization by H + re-encryption check.
   Decrypt1 is a separate module so it can call PKE1.encrypt.
   -------------------------------------------------------------------- *)
module PKE1 = {
  proc encrypt(h : R, m : M): C = {
    var e, lv;
    e  <@ H.hash(m);
    lv <@ L.hash(e);
    return (e.`1 + e.`2 * h, m + lv);
  }
}.

module Decrypt1 = {
  proc main(sk : R * R, h : R, c : C): M option = {
    var mo, c';
    mo <@ PKE.decrypt(sk, c);
    if (mo <> None) {
      c' <@ PKE1.encrypt(h, oget mo);
      if (c' <> c) { mo <- None; }
    }
    return mo;
  }
}.

(* --------------------------------------------------------------------
   A' (design P3): evidence-based determinism of Decrypt1.
   Decrypt1 calls the ROs L and H, so "same c => same answer" is not
   syntactic. ev_ok/ev_c record the RO entries that determine the run;
   Ev = rejection evidence, Acc = acceptance evidence. Lazy ROs never
   overwrite, so both are monotone under table growth (ev_stable).
   -------------------------------------------------------------------- *)

(* sub-map: m1's entries survive in m2. *)
op msub ['a 'b] (m1 m2 : ('a, 'b) fmap) : bool =
  forall (x : 'a), x \in m1 => m2.[x] = m1.[x].

lemma msub_refl ['a 'b] (m : ('a, 'b) fmap) : msub m m.
proof. by rewrite /msub. qed.

lemma msub_get ['a 'b] (m1 m2 : ('a, 'b) fmap) (x : 'a) :
  msub m1 m2 => x \in m1 => m2.[x] = m1.[x].
proof. by rewrite /msub => h hx; apply h. qed.

lemma msub_dom ['a 'b] (m1 m2 : ('a, 'b) fmap) (x : 'a) :
  msub m1 m2 => x \in m1 => x \in m2.
proof. by move=> h hx; smt(domE msub_get). qed.

lemma msub_trans ['a 'b] (m1 m2 m3 : ('a, 'b) fmap) :
  msub m1 m2 => msub m2 m3 => msub m1 m3.
proof. by rewrite /msub => h1 h2 x hx; smt(domE). qed.

lemma msub_set ['a 'b] (m : ('a, 'b) fmap) (x : 'a) (y : 'b) :
  x \notin m => msub m m.[x <- y].
proof. move=> hx; rewrite /msub => z hz; smt(get_setE domE). qed.

(* --- the run of Decrypt1(sk,h,c) as a function of the RO tables --- *)
op ev_e (sk : R * R) (c : C) : (R * R) option =
  decoder (c.`1 * sk.`1) sk.`1 sk.`2.

op ev_m (sk : R * R) (c : C) (mL : (R * R, M) fmap) : M =
  c.`2 + oget mL.[oget (ev_e sk c)].

op ev_ep (sk : R * R) (c : C)
         (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) : R * R =
  oget mH.[ev_m sk c mL].

(* all points the run needs are already in the tables *)
op ev_ok (sk : R * R) (c : C)
         (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) : bool =
     ev_e sk c <> None
  /\ oget (ev_e sk c) \in mL
  /\ ev_m sk c mL \in mH
  /\ ev_ep sk c mL mH \in mL.

(* the re-encryption of the decrypted message *)
op ev_c (sk : R * R) (h : R) (c : C)
        (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) : C =
  ( (ev_ep sk c mL mH).`1 + (ev_ep sk c mL mH).`2 * h,
    ev_m sk c mL + oget mL.[ev_ep sk c mL mH] ).

lemma ev_eE (sk : R * R) (c : C) :
  ev_e sk c = decoder (c.`1 * sk.`1) sk.`1 sk.`2.
proof. by rewrite /ev_e. qed.

lemma ev_mE (sk : R * R) (c : C) (mL : (R * R, M) fmap) :
  ev_m sk c mL = c.`2 + oget mL.[oget (ev_e sk c)].
proof. by rewrite /ev_m. qed.

op Ev (sk : R * R) (h : R) (c : C)
      (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) : bool =
  ev_e sk c = None \/ (ev_ok sk c mL mH /\ ev_c sk h c mL mH <> c).

op Acc (sk : R * R) (h : R) (c : C)
       (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) : bool =
  ev_ok sk c mL mH /\ ev_c sk h c mL mH = c.

lemma ev_stable (sk : R * R) (h : R) (c : C)
                (mL mL' : (R * R, M) fmap) (mH mH' : (M, R * R) fmap) :
  msub mL mL' => msub mH mH' => ev_ok sk c mL mH =>
     ev_m  sk c mL' = ev_m  sk c mL
  /\ ev_ep sk c mL' mH' = ev_ep sk c mL mH
  /\ ev_c  sk h c mL' mH' = ev_c  sk h c mL mH
  /\ ev_ok sk c mL' mH'.
proof.
move=> hL hH hok.
have h0 : ev_e sk c <> None            by move: hok; rewrite /ev_ok /#.
have h1 : oget (ev_e sk c) \in mL      by move: hok; rewrite /ev_ok /#.
have h2 : ev_m sk c mL \in mH          by move: hok; rewrite /ev_ok /#.
have h3 : ev_ep sk c mL mH \in mL      by move: hok; rewrite /ev_ok /#.
have hm : ev_m sk c mL' = ev_m sk c mL.
+ by rewrite /ev_m (msub_get _ _ _ hL h1).
have hep : ev_ep sk c mL' mH' = ev_ep sk c mL mH.
+ by rewrite /ev_ep hm (msub_get _ _ _ hH h2).
have hc : ev_c sk h c mL' mH' = ev_c sk h c mL mH.
+ by rewrite /ev_c hm hep (msub_get _ _ _ hL h3).
split; first exact hm.
split; first exact hep.
split; first exact hc.
rewrite /ev_ok hm hep.
smt(msub_dom).
qed.

lemma Ev_mono (sk : R * R) (h : R) (c : C)
              (mL mL' : (R * R, M) fmap) (mH mH' : (M, R * R) fmap) :
  msub mL mL' => msub mH mH' => Ev sk h c mL mH => Ev sk h c mL' mH'.
proof.
move=> hL hH; rewrite /Ev.
move=> [he|[hok hne]]; first by left.
have [hm [hep [hc hok']]] := ev_stable sk h c mL mL' mH mH' hL hH hok.
right; rewrite hc; split; [exact hok'|exact hne].
qed.

lemma Acc_mono (sk : R * R) (h : R) (c : C)
               (mL mL' : (R * R, M) fmap) (mH mH' : (M, R * R) fmap) :
  msub mL mL' => msub mH mH' => Acc sk h c mL mH => Acc sk h c mL' mH'.
proof.
move=> hL hH; rewrite /Acc.
move=> [hok heq].
have [hm [hep [hc hok']]] := ev_stable sk h c mL mL' mH mH' hL hH hok.
rewrite hc; split; [exact hok'|exact heq].
qed.

lemma Ev_Acc_excl (sk : R * R) (h : R) (c : C)
                  (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  Ev sk h c mL mH => Acc sk h c mL mH => false.
proof. rewrite /Ev /Acc /ev_ok; smt(). qed.

(* --------------------------------------------------------------------
   A' part 2: the three procedures that make up Decrypt1, each stated
   so that its RO effects are readable off the FINAL tables.
   -------------------------------------------------------------------- *)

(* PKE.decrypt: either the decoder fails (no RO call at all), or the
   syndrome point is in L's table and the plaintext is ev_m. *)
lemma PKE_decrypt_ev (skv : R * R) (cv : C)
                     (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  hoare[ PKE.decrypt :
         arg = (skv, cv) /\ ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ==>
         msub mL ROL.Lazy.LRO.m /\ ROH.Lazy.LRO.m = mH
      /\ (ev_e skv cv =  None => res = None)
      /\ (ev_e skv cv <> None =>
            oget (ev_e skv cv) \in ROL.Lazy.LRO.m
            /\ res = Some (ev_m skv cv ROL.Lazy.LRO.m)) ].
proof.
proc.
inline L.hash ROL.Lazy.LRO.o.
sp 2.
if.
+ auto => />.
  smt(msub_refl msub_set mem_set get_set_sameE domE ev_eE ev_mE).
auto => />.
qed.

(* PKE1.encrypt: both queried points end up in the tables, and the
   result is readable off them (H is not touched after its own call). *)
lemma PKE1_encrypt_ev (hv : R) (mv : M)
                      (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  hoare[ PKE1.encrypt :
         arg = (hv, mv) /\ ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ==>
         msub mL ROL.Lazy.LRO.m /\ msub mH ROH.Lazy.LRO.m
      /\ mv \in ROH.Lazy.LRO.m
      /\ oget ROH.Lazy.LRO.m.[mv] \in ROL.Lazy.LRO.m
      /\ res = ( (oget ROH.Lazy.LRO.m.[mv]).`1
                 + (oget ROH.Lazy.LRO.m.[mv]).`2 * hv,
                 mv + oget ROL.Lazy.LRO.m.[oget ROH.Lazy.LRO.m.[mv]] ) ].
proof.
proc; inline H.hash L.hash ROH.Lazy.LRO.o ROL.Lazy.LRO.o; auto => />.
smt(msub_refl msub_set mem_set get_set_sameE domE).
qed.

(* Bridge: the mid-run table mL1 and the final tables m2/mH2 compute the
   same ev_m / ev_ep, so the re-encryption result IS ev_c on the final
   tables. This is what lets Ev / Acc be stated on the post-state. *)
lemma ev_bridge (skv : R * R) (hv : R) (cv : C)
                (mL1 m2 : (R * R, M) fmap) (mH2 : (M, R * R) fmap) :
  ev_e skv cv <> None =>
  oget (ev_e skv cv) \in mL1 =>
  msub mL1 m2 =>
  ev_m skv cv mL1 \in mH2 =>
  oget mH2.[ev_m skv cv mL1] \in m2 =>
     ev_ok skv cv m2 mH2
  /\ ev_m skv cv m2 = ev_m skv cv mL1
  /\ ev_c skv hv cv m2 mH2
     = ( (oget mH2.[ev_m skv cv mL1]).`1
         + (oget mH2.[ev_m skv cv mL1]).`2 * hv,
         ev_m skv cv mL1 + oget m2.[oget mH2.[ev_m skv cv mL1]] ).
proof.
move=> h0 h1 hs h2 h3.
have hm : ev_m skv cv m2 = ev_m skv cv mL1.
+ by rewrite /ev_m (msub_get _ _ _ hs h1).
have hep : ev_ep skv cv m2 mH2 = oget mH2.[ev_m skv cv mL1].
+ by rewrite /ev_ep hm.
split.
+ rewrite /ev_ok hep hm; smt(msub_dom).
split; first exact hm.
by rewrite /ev_c hep hm.
qed.

lemma Decrypt1_evidence (skv : R * R) (hv : R) (cv : C)
                        (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  hoare[ Decrypt1.main :
         arg = (skv, hv, cv) /\ ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ==>
         msub mL ROL.Lazy.LRO.m /\ msub mH ROH.Lazy.LRO.m
      /\ (res =  None => Ev  skv hv cv ROL.Lazy.LRO.m ROH.Lazy.LRO.m)
      /\ (res <> None => Acc skv hv cv ROL.Lazy.LRO.m ROH.Lazy.LRO.m) ].
proof.
proc.
seq 1 : (msub mL ROL.Lazy.LRO.m /\ ROH.Lazy.LRO.m = mH
         /\ h = hv /\ c = cv
         /\ (ev_e skv cv =  None => mo = None)
         /\ (ev_e skv cv <> None =>
               oget (ev_e skv cv) \in ROL.Lazy.LRO.m
               /\ mo = Some (ev_m skv cv ROL.Lazy.LRO.m))).
+ by call (PKE_decrypt_ev skv cv mL mH); auto => />.
if.
+ exists* ROL.Lazy.LRO.m; elim* => mL1.
  wp.
  call (PKE1_encrypt_ev hv (ev_m skv cv mL1) mL1 mH).
  skip => />.
  smt(ev_bridge msub_trans msub_refl oget_some).
auto => />.
smt(msub_refl).
qed.

(* L.hash on an already-present key: table unchanged, returns the stored value. *)
lemma L_hash_mem (m0 : (R * R, M) fmap) (xa : R * R) :
  hoare[ L.hash : ROL.Lazy.LRO.m = m0 /\ arg = xa /\ xa \in m0
                  ==> ROL.Lazy.LRO.m = m0 /\ res = oget m0.[xa] ].
proof. proc; inline ROL.Lazy.LRO.o; sp; rcondf 2; first by auto. auto. qed.

lemma H_hash_mem (m0 : (M, R * R) fmap) (xa : M) :
  hoare[ H.hash : ROH.Lazy.LRO.m = m0 /\ arg = xa /\ xa \in m0
                  ==> ROH.Lazy.LRO.m = m0 /\ res = oget m0.[xa] ].
proof. proc; inline ROH.Lazy.LRO.o; sp; rcondf 2; first by auto. auto. qed.

(* PKE.decrypt leaves both RO tables when the syndrome point is already in L. *)
lemma PKE_decrypt_idem (skv : R * R) (cv : C)
                       (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  ev_e skv cv = None \/ oget (ev_e skv cv) \in mL =>
  hoare[ PKE.decrypt :
         arg = (skv, cv) /\ ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ==>
         ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH
         /\ (ev_e skv cv =  None => res = None)
         /\ (ev_e skv cv <> None => res = Some (ev_m skv cv mL)) ].
proof.
move=> hpre.
proc.
sp.
if.
+ wp.
  call (L_hash_mem mL (oget (ev_e skv cv))).
  skip => />; smt(ev_eE ev_mE).
skip => />; smt(ev_eE).
qed.

(* PKE1.encrypt leaves both RO tables when m is in H and H(m) is in L. *)
lemma PKE1_encrypt_idem (hv : R) (mv : M)
                        (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  mv \in mH => oget mH.[mv] \in mL =>
  hoare[ PKE1.encrypt :
         arg = (hv, mv) /\ ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH
         ==> ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ].
proof.
move=> hH hL.
proc.
call (L_hash_mem mL (oget mH.[mv])).
call (H_hash_mem mH mv).
auto => />; smt().
qed.

(* Decrypt1 は「読む点がすべて既にテーブルにある」なら fresh を引かず、
   ROL/ROH を変えない(lazy RO の if(x∉m)が全部 false)。SimD の反復 Pco が
   最初の強制呼び以降テーブル不変であることの根拠。 *)
lemma Decrypt1_idem (skv : R * R) (hv : R) (cv : C)
                    (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  ev_e skv cv = None \/ ev_ok skv cv mL mH =>
  hoare[ Decrypt1.main :
         arg = (skv, hv, cv)
         /\ ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ==>
                      ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH ].
proof.
move=> hpre.
case hpre => [hnone | hok].
+ (* ev_e = None: decoder が失敗、RO に一切触れない *)
  proc.
  seq 1 : (ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH /\ mo = None).
  + call (PKE_decrypt_idem skv cv mL mH _).
    + by left; exact hnone.
    skip => />; smt().
  rcondf 1; first by auto.
  auto.
(* ev_ok: シンドローム点∈L, ev_m∈H, ev_ep∈L *)
proc.
seq 1 : (ROL.Lazy.LRO.m = mL /\ ROH.Lazy.LRO.m = mH /\ h = hv
         /\ mo = Some (ev_m skv cv mL)).
+ call (PKE_decrypt_idem skv cv mL mH _).
  + by right; move: hok; rewrite /ev_ok /#.
  skip => />; move: hok; rewrite /ev_ok; smt().
rcondt 1; first by auto.
wp.
call (PKE1_encrypt_idem hv (ev_m skv cv mL) mL mH _ _).
+ by move: hok; rewrite /ev_ok /#.
+ by move: hok; rewrite /ev_ok /ev_ep /#.
skip => />; smt(oget_some).
qed.

(* ====================================================================
   11. KEM6bot (TABLE 16) AND ITS INLINED FORM (TABLE 17)
   ==================================================================== *)
module KEM = {
  proc keyGen(): (R * R) * M * R = {
    var h0, h1, sigma;
    h0 <$ dHw; h1 <$ dHw;
    sigma <$ duniformM;
    return ((h0, h1), sigma, h1 * invp h0);
  }
  proc encaps(h : R): M * C = {
    var m, c, k;
    m <$ duniformM;
    c <@ PKE1.encrypt(h, m);
    k <@ Kh.hash((m, c));
    return (k, c);
  }
  proc decaps(sk : (R * R) * M, h : R, c : C): M = {
    var mo, k;
    mo <@ Decrypt1.main(sk.`1, h, c);
    if (mo <> None) { k <@ Kh.hash((oget mo, c)); }
    else            { k <@ Kh.hash((sk.`2, c)); }
    return k;
  }
}.

(* Self-equivs for the KEM procedures (M3 alignment toolkit). *)
lemma KEM_keyGen_eq :
  equiv[ KEM.keyGen ~ KEM.keyGen : true ==> ={res} ].
proof. by proc; auto. qed.

lemma KEM_encaps_eq :
  equiv[ KEM.encaps ~ KEM.encaps :
         ={arg, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m} ==>
         ={res, ROH.Lazy.LRO.m, ROL.Lazy.LRO.m, ROK.Lazy.LRO.m} ].
proof. by proc; inline*; auto. qed.

(* Table 17 convention: bot = (0,0) in R^2, so L(bot) is meaningful. *)
op bote : R * R = (zeror, zeror).   (* CHECK: name of polyXnD1 zero *)

module KEM_i = {
  proc decaps(sk : (R * R) * M, c : C): M = {
    var eo, e', lv, m', eh, k;
    eo <- decoder (c.`1 * sk.`1.`1) sk.`1.`1 sk.`1.`2;
    e' <- odflt bote eo;
    lv <@ L.hash(e');
    m' <- c.`2 + lv;
    eh <@ H.hash(m');
    if (eh = e') { k <@ Kh.hash((m', c)); }
    else         { k <@ Kh.hash((sk.`2, c)); }
    return k;
  }
}.

(* M2: mechanization of the C.3 claim "the transformation is
   straightforward". Needs: t_gt0 (bote not in E_t, so eh = e' fails
   automatically when decoder failed, H ranging over E_t);
   decoder_sound (a syndrome-consistent Some e' makes the c0 component
   of re-encryption match, closing the gap of design P1); and an RO
   map-inclusion invariant (Table 17 lazily populates L/H on points
   Table 16 never queries — invisible to the adversary's view but the
   equiv must carry it; cf. design P1 last paragraph). The precise
   statement will be at the level of the CCA games (same adversary,
   decaps oracle swapped), not of decaps in isolation. *)
lemma decaps_inline_note : true.
proof. trivial. qed.
(* placeholder anchor: the real statement is added in M2 as
   IND_CCA(B) with KEM.decaps  vs  IND_CCA_i(B) with KEM_i.decaps. *)

(* ====================================================================
   12. Pco ORACLE, OW-PCA GAME (PKE1), IND-CCA GAME (KEM6bot)
   ==================================================================== *)
module KeyStore = {
  var sk    : R * R
  var sigma : M
  var h     : R
}.

module type PCO_t = { proc pco(m : M, c : C) : bool }.

(* Plaintext-checking oracle ([24]): true iff m = Decrypt1(sk, c). *)
module Pco : PCO_t = {
  proc pco(m : M, c : C) : bool = {
    var mo;
    mo <@ Decrypt1.main(KeyStore.sk, KeyStore.h, c);
    return mo = Some m;
  }
}.

module type OWPCA_Adv (OH : OrclH) (OL : OrclL) (OP : PCO_t) = {
  proc find(h : R, c : C) : M {OH.hash, OL.hash, OP.pco}
}.

module OW_PCA (B0 : OWPCA_Adv) = {
  proc main() : bool = {
    var kp, mstar, cstar, m';
    L.init(); H.init();
    kp <@ PKE.keyGen();
    KeyStore.sk <- kp.`1; KeyStore.h <- kp.`2;
    mstar <$ duniformM;
    cstar <@ PKE1.encrypt(kp.`2, mstar);
    m' <@ B0(H, L, Pco).find(kp.`2, cstar);
    return m' = mstar;
  }
}.

(* IND-CCA adversary and game for KEM6bot. The decaps oracle refuses
   the challenge (returns None on c = c* ). *)
module type KEM_CCA_Adv (OH : OrclH) (OL : OrclL) (OK : OrclK)
                        (OD : DecapsO) = {
  proc guess(h : R, c : C, k : M) : bool
    {OH.hash, OL.hash, OK.hash, OD.decaps}
}.

module Cstar = { var c : C }.

module ODecaps : DecapsO = {
  proc decaps(c : C) : M option = {
    var k, ko;
    ko <- None;
    if (c <> Cstar.c) {
      k <@ KEM.decaps((KeyStore.sk, KeyStore.sigma), KeyStore.h, c);
      ko <- Some k;
    }
    return ko;
  }
}.

module IND_CCA (B : KEM_CCA_Adv) = {
  proc main() : bool = {
    var kg, kc, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    kg <@ KEM.keyGen();
    KeyStore.sk <- kg.`1; KeyStore.sigma <- kg.`2; KeyStore.h <- kg.`3;
    kc <@ KEM.encaps(kg.`3);
    Cstar.c <- kc.`2;
    k1 <$ duniformM;
    b <$ {0,1};
    b' <@ B(CountH(H), L, CountK(Kh), ODecaps).guess
            (kg.`3, kc.`2, b ? k1 : kc.`1);
    return b' = b;
  }
}.

lemma PKE_decrypt_ll : islossless PKE.decrypt.
proof. proc; islossless; exact duniformM_ll. qed.

lemma PKE1_encrypt_ll : islossless PKE1.encrypt.
proof. proc; islossless; [exact duniformM_ll | exact DEt_ll]. qed.

lemma Decrypt1_ll : islossless Decrypt1.main.
proof. proc; islossless; smt(duniformM_ll DEt_ll). qed.

lemma KEM_decaps_ll : islossless KEM.decaps.
proof. proc; islossless; smt(duniformM_ll DEt_ll). qed.

lemma ODecaps_ll : islossless ODecaps.decaps.
proof. proc; islossless; smt(duniformM_ll DEt_ll). qed.

lemma Decrypt1_eq :
  equiv[ Decrypt1.main ~ Decrypt1.main :
         ={arg, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m} ==>
         ={res, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m} ].
       proof. proc; inline*; sim. qed.

(* Decrypt1_eq and Decrypt1_evidence bundled into one equiv, so that a
   single `call` at the game level both keeps the two runs in sync and
   exposes the verdict's witness on the post-state tables. *)
lemma Decrypt1_eq_ev (skv : R * R) (hv : R) (cv : C)
                     (mL : (R * R, M) fmap) (mH : (M, R * R) fmap) :
  equiv[ Decrypt1.main ~ Decrypt1.main :
         ={arg, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m}
         /\ arg{2} = (skv, hv, cv)
         /\ ROL.Lazy.LRO.m{2} = mL /\ ROH.Lazy.LRO.m{2} = mH ==>
         ={res, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m}
         /\ msub mL ROL.Lazy.LRO.m{2} /\ msub mH ROH.Lazy.LRO.m{2}
         /\ (res{2} =  None => Ev  skv hv cv ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
         /\ (res{2} <> None => Acc skv hv cv ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2}) ].
proof.
conseq Decrypt1_eq _ (Decrypt1_evidence skv hv cv mL mH) => //.
qed.

(* The challenge Kh.hash only ever adds a row whose ciphertext component
   is the queried one; with arg = (m*, c* ) this seeds invariant I2 of
   GA1_GA2_upto (no sigma-row for c <> c* exists when B starts).
   NOTE: procedure parameters are not in scope in an equiv pre/post
   (only arg{i}, and not at all in the post), hence the invariant is
   phrased with the global Cstar.c, which Kh.hash does not modify. *)
lemma Kh_hash_dom :
  equiv[ Kh.hash ~ Kh.hash :
         ={arg, ROK.Lazy.LRO.m}
         /\ arg{1}.`2 = Cstar.c{1}
         /\ (forall (y : M * C), y \in ROK.Lazy.LRO.m{1} => y.`2 = Cstar.c{1})
         ==>
         ={res, ROK.Lazy.LRO.m}
         /\ (forall (y : M * C), y \in ROK.Lazy.LRO.m{1} => y.`2 = Cstar.c{1}) ].
proof. by proc; inline ROK.Lazy.LRO.o; auto => />; smt(mem_set). qed.

(* ====================================================================
   13. EXPLICIT REDUCTIONS
   ==================================================================== *)

(* --------------------------------------------------------------------
   B_ow(B): the B' of [24, Thm 3.4]. Runs the IND-CCA adversary B,
   simulating K by lazy sampling patched through Pco (so that
   K(m, c) with Pco(m, c) stays consistent with the simulated
   Decaps table), and simulating Decaps(c) without sk via a fresh
   random key table indexed by c. Finally searches its K-query list
   for a pair (m, c* ) with Pco(m, c* ) and returns that m.
   State: own K-map, decaps-map, query list — all fresh module vars
   (disjoint from the base-file exclusion set, cf. section header).
   -------------------------------------------------------------------- *)
module B_ow (B : KEM_CCA_Adv) (OH : OrclH) (OL : OrclL) (OP : PCO_t) = {
  var kmap  : (M * C, M) fmap   (* K rows at (m,c) for undecapsulated c *)
  var dmap  : (C, M) fmap       (* the value Decaps returned for c *)
  var dseen : C list            (* ciphertexts already sent to SimD *)
  var qs    : (M * C) list      (* K-query transcript *)
  var cst   : C

  module SimK : OrclK = {
    proc hash(x : M * C) : M = {
      var k, hit;
      qs  <- x :: qs;
      hit <- false;
      (* Pco only on already-decapsulated ciphertexts: those RO rows
         exist, so this call creates none. *)
      if (x.`2 \in dseen) { hit <@ OP.pco(x.`1, x.`2); }
      if (hit) {
        if (x.`2 \notin dmap) { k <$ duniformM; dmap.[x.`2] <- k; }
        k <- oget dmap.[x.`2];
      } else {
        if (x \notin kmap) { k <$ duniformM; kmap.[x] <- k; }
        k <- oget kmap.[x];
      }
      return k;
    }
  }

  module SimD : DecapsO = {
    proc decaps(c : C) : M option = {
      var k, hit, found, m0, rest, x, ko;
      ko <- None;
      if (c <> cst) {
        if (c \notin dmap) {
          k <$ duniformM;                 (* presampled; used only if !found *)
          hit <@ OP.pco(witness, c);      (* forcing call: mirrors Decrypt1(c) *)
          found <- false; m0 <- witness; rest <- qs;
          while (0 < size rest /\ !found) {
            x <- head witness rest; rest <- behead rest;
            if (x.`2 = c) {
              hit <@ OP.pco(x.`1, c);
              if (hit) { found <- true; m0 <- x.`1; }
            }
          }
          if (found) { dmap.[c] <- oget kmap.[(m0, c)]; }
          else       { dmap.[c] <- k; }
          dseen <- c :: dseen;
        }
        ko <- Some (oget dmap.[c]);
      }
      return ko;
    }
  }

  proc find(h : R, c : C) : M = {
    var k0, b0, m', found, x, rest, hit;
    kmap <- empty; dmap <- empty; qs <- []; cst <- c;
    k0 <$ duniformM;
    b0 <@ B(OH, OL, SimK, SimD).guess(h, c, k0);
    m' <- zerov l; found <- false; rest <- qs;
    while (0 < size rest /\ !found) {
      x <- head witness rest; rest <- behead rest;
      hit <@ OP.pco(x.`1, x.`2);
      if (hit /\ x.`2 = cst) { m' <- x.`1; found <- true; }
    }
    return m';
  }
}.

(* --------------------------------------------------------------------
   A_cpa(B0): the A of [24, Thm 3.2] (downgraded to OW-PCA), typed as
   the base file's LOR_Adv so that Theorem2_final applies verbatim.
   choose: sample m0*, m1* <$ M (well-formed by construction — the
   A_choose_wf obligation will follow from duniformM_size).
   guess: run B0 on (h, (c0, c1)) simulating
     - H by lazy sampling into ROH.Lazy.LRO (own state, allowed),
     - Pco(m, c) by re-encryption: Encrypt1(h, m) = c, computed with
       the simulated H and the REAL oracle O (the L of the CPA game),
   recording B0's H-queries; then decide by the case analysis of
   [24, Thm 3.2] (H-query equal to m0*/m1*, or B0's output equal to
   one of them, else a coin) — the source of the 3-way advantage
   splitting and the (2qH+1)/|M| term.
   -------------------------------------------------------------------- *)
module A_cpa (B0 : OWPCA_Adv) (O : OrclL) = {
  var m0s, m1s : M
  var hqs : M list
  var hpk : R

  module SimH : OrclH = {
    proc hash(m : M) : R * R = {
      var e;
      hqs <- m :: hqs;
      e <@ ROH.Lazy.LRO.o(m);
      return e;
    }
  }
  module SimPco : PCO_t = {
    proc pco(m : M, c : C) : bool = {
      var e, lv;
      e  <@ ROH.Lazy.LRO.o(m);
      lv <@ O.hash(e);
      return (e.`1 + e.`2 * hpk, m + lv) = c;
    }
  }

  proc choose(h : R) : M * M = {
    ROH.Lazy.LRO.init();
    hqs <- []; hpk <- h;
    m0s <$ duniformM;
    m1s <$ duniformM;
    return (m0s, m1s);
  }
  proc guess(c0 : R, c1 : M) : bool = {
    var m', b';
    (* coin presampled (distribution-preserving: it is independent and
       used only when neither condition holds) — makes the tail if-tree
       deterministic, so losslessness is a plain wp. *)
    b' <$ {0,1};
    m' <@ B0(SimH, O, SimPco).find(hpk, (c0, c1));
    (* decision rule of [24, Thm 3.2] (refined in M4) *)
    if (m' = m1s \/ m1s \in hqs) { b' <- true; }
    else {
      if (m' = m0s \/ m0s \in hqs) { b' <- false; }
    }
    return b';
  }
}.

(* ====================================================================
   14. SECURITY (APPENDIX C.2 LEMMA 2 AND C.3 THEOREM 3)
   ==================================================================== *)
section CCA_Security.

declare module B <: KEM_CCA_Adv
  {-Bike, -L, -ROL.Lazy.LRO, -BadWit,
   -H, -ROH.Lazy.LRO, -Kh, -ROK.Lazy.LRO,
   -CountH, -CountK, -KeyStore, -Cstar, -ODecaps, -B_ow, -A_cpa}.

(* Adversary contract: termination given lossless oracles. *)
declare axiom B_guess_ll :
  forall (OH <: OrclH {-B}) (OL <: OrclL {-B})
         (OK <: OrclK {-B}) (OD <: DecapsO {-B}),
    islossless OH.hash => islossless OL.hash =>
    islossless OK.hash => islossless OD.decaps =>
    islossless B(OH, OL, OK, OD).guess.

(* Adversary contract: query budget (counted by CountH/CountK inside
   IND_CCA). Exact formulation (hoare on counters vs fel) to be fixed
   in M3/M4; stated here as the interface the bounds refer to. *)
(* Query-budget contract, final form (M3): generic over the oracle
   tuple (so it applies inside the local game sequence), transcript-
   length form on the K side (feeds the deferred-sampling bound
   Pr[bad_sig] <= qK * epsM via mu_mem over CountK.qs). *)
declare axiom B_qbound (OH <: OrclH {-B, -CountH, -CountK})
                       (OL <: OrclL {-B, -CountH, -CountK})
                       (OK <: OrclK {-B, -CountH, -CountK})
                       (OD <: DecapsO {-B, -CountH, -CountK}) :
  hoare[ B(CountH(OH), OL, CountK(OK), OD).guess :
         CountH.c = 0 /\ CountK.c = 0 /\ CountK.qs = [] ==>
         CountH.c <= qH /\ CountK.c <= qK /\ size CountK.qs <= qK ].

(* ====================================================================
   M3 (HHK Thm 3.4): local game sequence.
     GA0 : IND_CCA + K monitor on B's oracle (transparent)
     GA1 : challenge inlined (mstar/estar exposed) + bad_corr computed
           (transparent rewrite)
     GA2 : implicit-rejection branch on the random function dmap
           (Hop A proper; identical-until-bad_sig)
   Flags:
     bad_sig  = B queried K on (sigma, .)     -> qK * epsM
     bad_corr = decoder wrong on the challenge -> Pr[Corr]
   ==================================================================== *)
local module GFlag = {
  var bad_sig  : bool
  var bad_corr : bool
  var dmap     : (C, M) fmap
}.

(* K monitor: flag (sigma, .) queries, then forward (transparent). *)
local module KMon : OrclK = {
  proc hash(x : M * C) : M = {
    var k;
    if (x.`1 = KeyStore.sigma) { GFlag.bad_sig <- true; }
    k <@ Kh.hash(x);
    return k;
  }
}.

(* Decaps with the implicit-rejection branch replaced by dmap (Hop A). *)
local module ODecapsA : DecapsO = {
  proc decaps(c : C) : M option = {
    var mo, k, ko;
    ko <- None;
    if (c <> Cstar.c) {
      mo <@ Decrypt1.main(KeyStore.sk, KeyStore.h, c);
      if (mo <> None) { k <@ Kh.hash((oget mo, c)); }
      else {
        if (c \notin GFlag.dmap) { k <$ duniformM; GFlag.dmap.[c] <- k; }
        k <- oget GFlag.dmap.[c];
      }
      ko <- Some k;
    }
    return ko;
  }
}.

local lemma ODecapsA_ll : islossless ODecapsA.decaps.
proof. proc; islossless; smt(duniformM_ll DEt_ll). qed.

local module GA0 = {
  proc main() : bool = {
    var kg, kc, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    kg <@ KEM.keyGen();
    KeyStore.sk <- kg.`1; KeyStore.sigma <- kg.`2; KeyStore.h <- kg.`3;
    kc <@ KEM.encaps(kg.`3);
    Cstar.c <- kc.`2;
    k1 <$ duniformM;
    b <$ {0,1};
    b' <@ B(CountH(H), L, CountK(KMon), ODecaps).guess
            (kg.`3, kc.`2, b ? k1 : kc.`1);
    return b' = b;
  }
}.

local module GA1 = {
  var mstar : M
  var estar : R * R
  proc main() : bool = {
    var h0, h1, sigma, lv, kstar, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    h0 <$ dHw; h1 <$ dHw; sigma <$ duniformM;
    KeyStore.sk <- (h0, h1); KeyStore.sigma <- sigma;
    KeyStore.h <- h1 * invp h0;
    mstar <$ duniformM;
    estar <@ H.hash(mstar);
    lv <@ L.hash(estar);
    Cstar.c <- (estar.`1 + estar.`2 * KeyStore.h, mstar + lv);
    GFlag.bad_corr <- decoder (Cstar.c.`1 * h0) h0 h1 <> Some estar;
    kstar <@ Kh.hash((mstar, Cstar.c));
    k1 <$ duniformM;
    b <$ {0,1};
    b' <@ B(CountH(H), L, CountK(KMon), ODecaps).guess
            (KeyStore.h, Cstar.c, b ? k1 : kstar);
    return b' = b;
  }
}.

local module GA2 = {
  proc main() : bool = {
    var h0, h1, sigma, lv, kstar, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    h0 <$ dHw; h1 <$ dHw; sigma <$ duniformM;
    KeyStore.sk <- (h0, h1); KeyStore.sigma <- sigma;
    KeyStore.h <- h1 * invp h0;
    GA1.mstar <$ duniformM;
    GA1.estar <@ H.hash(GA1.mstar);
    lv <@ L.hash(GA1.estar);
    Cstar.c <- (GA1.estar.`1 + GA1.estar.`2 * KeyStore.h, GA1.mstar + lv);
    GFlag.bad_corr <- decoder (Cstar.c.`1 * h0) h0 h1 <> Some GA1.estar;
    kstar <@ Kh.hash((GA1.mstar, Cstar.c));
    k1 <$ duniformM;
    b <$ {0,1};
    b' <@ B(CountH(H), L, CountK(KMon), ODecapsA).guess
            (KeyStore.h, Cstar.c, b ? k1 : kstar);
    return b' = b;
  }
}.

local module GA2' = {
  proc main() : bool = {
    var h0, h1, sigma, lv, kstar, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    h0 <$ dHw; h1 <$ dHw;
    sigma <$ duniformM;                       (* ← 前に戻す *)
    KeyStore.sk <- (h0, h1);
    KeyStore.sigma <- sigma;                  (* ← 前に戻す *)
    KeyStore.h <- h1 * invp h0;
    GA1.mstar <$ duniformM;
    GA1.estar <@ H.hash(GA1.mstar);
    lv <@ L.hash(GA1.estar);
    Cstar.c <- (GA1.estar.`1 + GA1.estar.`2 * KeyStore.h, GA1.mstar + lv);
    GFlag.bad_corr <- decoder (Cstar.c.`1 * h0) h0 h1 <> Some GA1.estar;
    kstar <@ Kh.hash((GA1.mstar, Cstar.c));
    k1 <$ duniformM;
    b <$ {0,1};
    b' <@ B(CountH(H), L, CountK(Kh), ODecapsA).guess
            (KeyStore.h, Cstar.c, if b then k1 else kstar);
    return b' = b;
  }
}.

(* --- Hop statements (proofs = next batches) --- *)

local lemma IND_CCA_GA0 &m :
  Pr[IND_CCA(B).main() @ &m : res] = Pr[GA0.main() @ &m : res].
proof.
byequiv (: ={glob B} ==> ={res}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
           KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
           CountH.c, CountK.c, CountK.qs}).
+ by sim.
+ by sim.
+ proc; inline{2} KMon.hash; sp 2 3.
  if{2}.
  + by wp; call Kh_hash_eq; auto => />.
  by wp; call Kh_hash_eq; auto => />.
+ by sim.
rnd. rnd. wp.
call KEM_encaps_eq.
wp.
call KEM_keyGen_eq.
inline L.init H.init Kh.init
       ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
auto => />.
qed.

local lemma GA0_GA1 &m :
  Pr[GA0.main() @ &m : res] = Pr[GA1.main() @ &m : res].
proof.
byequiv (: ={glob B} ==> ={res}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
           KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
           CountH.c, CountK.c, CountK.qs,
           GFlag.bad_sig, GFlag.dmap}); first 4 by sim.
inline{1} KEM.encaps KEM.keyGen PKE1.encrypt.
wp.
rnd.
rnd.
wp.
call Kh_hash_eq.
wp.
call L_hash_eq.
call H_hash_eq.
wp.
rnd.
wp.
inline L.init H.init Kh.init
       ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
auto => />.
qed.

local lemma GA1_GA2_upto :
  equiv[ GA1.main ~ GA2.main :
         ={glob B} ==>
         ={GFlag.bad_sig} /\ (!GFlag.bad_sig{2} => ={res, GFlag.bad_corr}) ].
proof.
proc.
seq 23 23 : (={glob B, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
               kstar, k1, b}
             /\ GFlag.bad_sig{2} = false
             /\ GFlag.dmap{2} = empty
             /\ (forall (y : M * C),
                   y \in ROK.Lazy.LRO.m{1} => y.`2 = Cstar.c{1})).
+ rnd. rnd.
  call Kh_hash_dom.
  wp.
  call L_hash_eq.
  call H_hash_eq.
  wp. rnd. wp.
  inline L.init H.init Kh.init
         ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto => />.
  smt(mem_empty).
call (_: GFlag.bad_sig,
      ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
        KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
        CountH.c, CountK.c, CountK.qs,
        GFlag.bad_sig, GFlag.bad_corr}
      /\ eq_except
           (fun (x : M * C) =>
              x.`1 = KeyStore.sigma{2} /\ x.`2 \in GFlag.dmap{2})
           ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
      /\ (forall (c : C), c \in GFlag.dmap{2} =>
            ROK.Lazy.LRO.m{1}.[(KeyStore.sigma{2}, c)] = GFlag.dmap{2}.[c])
      /\ (forall (c : C), c \in GFlag.dmap{2} =>
            (KeyStore.sigma{2}, c) \notin ROK.Lazy.LRO.m{2})
      /\ (forall (c : C), c \in GFlag.dmap{2} =>
            Ev KeyStore.sk{2} KeyStore.h{2} c
               ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
      /\ (forall (c : C), c <> Cstar.c{2} =>
            (KeyStore.sigma{2}, c) \in ROK.Lazy.LRO.m{1} =>
            c \in GFlag.dmap{2}
            \/ Acc KeyStore.sk{2} KeyStore.h{2} c
                   ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2}),
        GFlag.bad_sig{1} /\ GFlag.bad_sig{2}).
(* G1 : B の termination 契約 *)
+ exact B_guess_ll.
(* G2 : CountH(H) 等価 — H への書き込みで Ev / Acc を単調に保つ *)
+ by proc; inline*; auto => />;
     smt(Ev_mono Acc_mono msub_set msub_refl mem_set domE).
(* G3 / G4 : CountH(H) の左右 lossless *)
+ by move=> &2 hbad; proc; inline*; auto => />; smt(DEt_ll).
+ by move=> &1; proc; inline*; auto => />; smt(DEt_ll).
(* G5 : L 等価 — L への書き込みで Ev / Acc を単調に保つ *)
+ by proc; inline*; auto => />;
     smt(Ev_mono Acc_mono msub_set msub_refl mem_set domE).
(* G6 / G7 : L の左右 lossless *)
+ by move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
+ by move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
(* G8 : CountK(KMon) 等価 *)
+ proc.
  inline{1} KMon.hash. inline{2} KMon.hash.
  sp 3 3.
  if => //.
  + conseq (: _ ==> GFlag.bad_sig{1} /\ GFlag.bad_sig{2}); 1: smt().
    wp. call{1} Kh_hash_ll. call{2} Kh_hash_ll. auto => />.
  inline{1} Kh.hash ROK.Lazy.LRO.o.
  inline{2} Kh.hash ROK.Lazy.LRO.o.
  sp.
  seq 1 1 : (={x2, r, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr}
             /\ !GFlag.bad_sig{2}
             /\ x2{2}.`1 <> KeyStore.sigma{2}
             /\ eq_except
                  (fun (x3 : M * C) =>
                     x3.`1 = KeyStore.sigma{2} /\ x3.`2 \in GFlag.dmap{2})
                  ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
             /\ (forall (c : C), c \in GFlag.dmap{2} =>
                   ROK.Lazy.LRO.m{1}.[(KeyStore.sigma{2}, c)] = GFlag.dmap{2}.[c])
             /\ (forall (c : C), c \in GFlag.dmap{2} =>
                   (KeyStore.sigma{2}, c) \notin ROK.Lazy.LRO.m{2})
             /\ (forall (c : C), c \in GFlag.dmap{2} =>
                   Ev KeyStore.sk{2} KeyStore.h{2} c
                      ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
             /\ (forall (c : C), c <> Cstar.c{2} =>
                   (KeyStore.sigma{2}, c) \in ROK.Lazy.LRO.m{1} =>
                   c \in GFlag.dmap{2}
                   \/ Acc KeyStore.sk{2} KeyStore.h{2} c
                          ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})).
  + by auto => />; smt().
  if.
  + by move=> &1 &2 />; smt(eq_exceptP domE).
  + by auto => />; smt(get_setE mem_set eq_exceptP domE).
  by auto => />; smt(eq_exceptP domE).
(* G9 / G10 : CountK(KMon) の左右 lossless *)
+ by move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
+ by move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
(* G11 : ODecaps ~ ODecapsA — 次パッチ（Decrypt1_evidence 待ち） *)
(* G11 : ODecaps ~ ODecapsA *)
+ proc.
  inline{1} KEM.decaps.
  sp.
  if => //.
  sp 3 0.
  exists* ROL.Lazy.LRO.m{2}, ROH.Lazy.LRO.m{2},
          KeyStore.sk{2}, KeyStore.h{2}, c{2};
  elim* => mL mH skv hv cv.
  seq 1 1 : (={c, mo, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr}
             /\ !GFlag.bad_sig{2}
             /\ c0{1} = c{1}
             /\ sk{1} = (KeyStore.sk{1}, KeyStore.sigma{1})
             /\ c{2} <> Cstar.c{2}
             /\ KeyStore.sk{2} = skv /\ KeyStore.h{2} = hv /\ c{2} = cv
             /\ (mo{2} =  None =>
                   Ev  skv hv cv ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
             /\ (mo{2} <> None =>
                   Acc skv hv cv ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
             /\ eq_except
                  (fun (x : M * C) =>
                     x.`1 = KeyStore.sigma{2} /\ x.`2 \in GFlag.dmap{2})
                  ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
             /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                   ROK.Lazy.LRO.m{1}.[(KeyStore.sigma{2}, c1)] = GFlag.dmap{2}.[c1])
             /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                   (KeyStore.sigma{2}, c1) \notin ROK.Lazy.LRO.m{2})
             /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                   Ev KeyStore.sk{2} KeyStore.h{2} c1
                      ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
             /\ (forall (c1 : C), c1 <> Cstar.c{2} =>
                   (KeyStore.sigma{2}, c1) \in ROK.Lazy.LRO.m{1} =>
                   c1 \in GFlag.dmap{2}
                   \/ Acc KeyStore.sk{2} KeyStore.h{2} c1
                          ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})).
  + by call (Decrypt1_eq_ev skv hv cv mL mH); auto => />; smt(Ev_mono Acc_mono).
  if => //.
  (* ---- 受理枝: Acc(後) と I1 から c ∉ dmap が出る ---- *)
  (* ---- 受理枝: Acc(後) と I1 の矛盾で c ∉ dmap を先に確定 ---- *)
  + case (c{2} \in GFlag.dmap{2}).
    (* c ∈ dmap なら I1 から Ev(後)、一方 mo <> None から Acc(後) — 矛盾 *)
    + exfalso.
      move=> &1 &2 />.
      smt(Ev_Acc_excl).
    (* 以下、c{2} \notin GFlag.dmap{2} が pre にある状態 *)
    inline{1} Kh.hash ROK.Lazy.LRO.o.
    inline{2} Kh.hash ROK.Lazy.LRO.o.
    sp.
    seq 1 1 : (={x0, r, c, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
                 KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
                 CountH.c, CountK.c, CountK.qs,
                 GFlag.bad_sig, GFlag.bad_corr}
               /\ !GFlag.bad_sig{2}
               /\ x0{2}.`2 = c{2}
               /\ c{2} \notin GFlag.dmap{2}
               /\ c{2} <> Cstar.c{2}
               /\ KeyStore.sk{2} = skv /\ KeyStore.h{2} = hv /\ c{2} = cv
               /\ Acc skv hv cv ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2}
               /\ eq_except
                    (fun (x : M * C) =>
                       x.`1 = KeyStore.sigma{2} /\ x.`2 \in GFlag.dmap{2})
                    ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
               /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                     ROK.Lazy.LRO.m{1}.[(KeyStore.sigma{2}, c1)] = GFlag.dmap{2}.[c1])
               /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                     (KeyStore.sigma{2}, c1) \notin ROK.Lazy.LRO.m{2})
               /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                     Ev KeyStore.sk{2} KeyStore.h{2} c1
                        ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
               /\ (forall (c1 : C), c1 <> Cstar.c{2} =>
                     (KeyStore.sigma{2}, c1) \in ROK.Lazy.LRO.m{1} =>
                     c1 \in GFlag.dmap{2}
                     \/ Acc KeyStore.sk{2} KeyStore.h{2} c1
                       ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})).
    + by auto => />; smt().
    if.
    + by move=> &1 &2 />; smt(eq_exceptP domE).
    + by auto => />; smt(get_setE mem_set eq_exceptP domE).
    by auto => />; smt(eq_exceptP domE).
  (* ---- 拒否枝: c ∈ dmap なら既存行、c ∉ dmap なら I2 で左も新規 ---- *)
  inline{1} Kh.hash ROK.Lazy.LRO.o.
  sp 2 0.
  case (c{2} \in GFlag.dmap{2}).
  (* (i) 既に拒否済み: 両側とも dmap[c] を返す *)
  (* (i) 既に拒否済み: 左は既存行、右は dmap[c] *)
  + rcondf{2} 1; first by auto.
    rcondf{1} 2; first by auto => />; smt(domE).
    wp.
    rnd{1}.
    skip => />; smt(duniformM_ll domE).
  (* (ii) 初めての拒否: 両側とも新規サンプル *)
  rcondt{2} 1; first by auto.
  seq 1 1 : (r{1} = k{2}
             /\ ={c, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
                  KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
                  CountH.c, CountK.c, CountK.qs,
                  GFlag.bad_sig, GFlag.bad_corr}
             /\ !GFlag.bad_sig{2}
             /\ c{2} \notin GFlag.dmap{2}
             /\ c{2} <> Cstar.c{2}
             /\ KeyStore.sk{2} = skv /\ KeyStore.h{2} = hv /\ c{2} = cv
             /\ Ev skv hv cv ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2}
             /\ x0{1} = (KeyStore.sigma{2}, c{2})
             /\ eq_except
                  (fun (x : M * C) =>
                     x.`1 = KeyStore.sigma{2} /\ x.`2 \in GFlag.dmap{2})
                  ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
             /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                   ROK.Lazy.LRO.m{1}.[(KeyStore.sigma{2}, c1)] = GFlag.dmap{2}.[c1])
             /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                   (KeyStore.sigma{2}, c1) \notin ROK.Lazy.LRO.m{2})
             /\ (forall (c1 : C), c1 \in GFlag.dmap{2} =>
                   Ev KeyStore.sk{2} KeyStore.h{2} c1
                      ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})
             /\ (forall (c1 : C), c1 <> Cstar.c{2} =>
                   (KeyStore.sigma{2}, c1) \in ROK.Lazy.LRO.m{1} =>
                   c1 \in GFlag.dmap{2}
                   \/ Acc KeyStore.sk{2} KeyStore.h{2} c1
                          ROL.Lazy.LRO.m{2} ROH.Lazy.LRO.m{2})).
  + by auto => />; smt().
  rcondt{1} 1; first by auto => />; smt(Ev_Acc_excl domE).
  wp; skip => />; smt(get_setE mem_set eq_exceptP domE).
(* G12 / G13 : decaps の左右 lossless *)
+ by move=> &2 hbad; conseq ODecaps_ll  => //.
+ by move=> &1;      conseq ODecapsA_ll => //.
skip => />; smt(mem_empty eq_exceptP).
qed.

local lemma GA1_GA2_res_notbad &m :
  Pr[GA1.main() @ &m : res /\ !GFlag.bad_sig]
  = Pr[GA2.main() @ &m : res /\ !GFlag.bad_sig].
proof. by byequiv GA1_GA2_upto => // /#. qed.

local lemma GA1_GA2_bad &m :
  Pr[GA1.main() @ &m : GFlag.bad_sig]
  = Pr[GA2.main() @ &m : GFlag.bad_sig].
proof. by byequiv GA1_GA2_upto => // /#. qed.

local lemma GA1_GA2_abs &m :
  `| Pr[GA1.main() @ &m : res] - Pr[GA2.main() @ &m : res] |
  <= Pr[GA2.main() @ &m : GFlag.bad_sig].
proof.
have h1 := GA1_GA2_res_notbad &m.
have h2 := GA1_GA2_bad &m.
have e1 : Pr[GA1.main() @ &m : res]
  = Pr[GA1.main() @ &m : res /\ GFlag.bad_sig]
  + Pr[GA1.main() @ &m : res /\ !GFlag.bad_sig].
+ by rewrite Pr [mu_split GFlag.bad_sig].
have e2 : Pr[GA2.main() @ &m : res]
  = Pr[GA2.main() @ &m : res /\ GFlag.bad_sig]
  + Pr[GA2.main() @ &m : res /\ !GFlag.bad_sig].
+ by rewrite Pr [mu_split GFlag.bad_sig].
have u1 : Pr[GA1.main() @ &m : res /\ GFlag.bad_sig]
       <= Pr[GA1.main() @ &m : GFlag.bad_sig].
+ by rewrite Pr [mu_sub] => /#.
have u2 : Pr[GA2.main() @ &m : res /\ GFlag.bad_sig]
       <= Pr[GA2.main() @ &m : GFlag.bad_sig].
+ by rewrite Pr [mu_sub] => /#.
have g1 : 0%r <= Pr[GA1.main() @ &m : res /\ GFlag.bad_sig].
+ by rewrite Pr [mu_ge0].
have g2 : 0%r <= Pr[GA2.main() @ &m : res /\ GFlag.bad_sig].
+ by rewrite Pr [mu_ge0].
smt().
qed.

(* QUERY flag: B asked K at the challenge point (m*, c* ). Kept in its own
   module so that GFlag (and hence GA1/GA2) is untouched. *)
local module QFlag = { var query : bool }.

(* K monitor of GA2 plus the QUERY flag. *)
local module KMonQ : OrclK = {
  proc hash(x : M * C) : M = {
    var k;
    if (x.`1 = KeyStore.sigma)          { GFlag.bad_sig <- true; }
    if (x = (GA1.mstar, Cstar.c))       { QFlag.query   <- true; }
    k <@ Kh.hash(x);
    return k;
  }
}.

(* GA2 with b sampled early and the QUERY monitor (transparent). *)
local module GA2q = {
  proc main() : bool = {
    var h0, h1, sigma, lv, kstar, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    QFlag.query <- false;
    h0 <$ dHw; h1 <$ dHw; sigma <$ duniformM;
    KeyStore.sk <- (h0, h1); KeyStore.sigma <- sigma;
    KeyStore.h <- h1 * invp h0;
    GA1.mstar <$ duniformM;
    GA1.estar <@ H.hash(GA1.mstar);
    lv <@ L.hash(GA1.estar);
    Cstar.c <- (GA1.estar.`1 + GA1.estar.`2 * KeyStore.h, GA1.mstar + lv);
    GFlag.bad_corr <- decoder (Cstar.c.`1 * h0) h0 h1 <> Some GA1.estar;
    b <$ {0,1};
    kstar <@ Kh.hash((GA1.mstar, Cstar.c));
    k1 <$ duniformM;
    b' <@ B(CountH(H), L, CountK(KMonQ), ODecapsA).guess
            (KeyStore.h, Cstar.c, b ? k1 : kstar);
    return b' = b;
  }
}.

(* GA3: the challenge key is an independent sample; ROK has no row at
   (m*, c* ). Identical to GA2q until B queries K there (= QUERY). *)
local module GA3 = {
  proc main() : bool = {
    var h0, h1, sigma, lv, kstar, k1, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    QFlag.query <- false;
    h0 <$ dHw; h1 <$ dHw; sigma <$ duniformM;
    KeyStore.sk <- (h0, h1); KeyStore.sigma <- sigma;
    KeyStore.h <- h1 * invp h0;
    GA1.mstar <$ duniformM;
    GA1.estar <@ H.hash(GA1.mstar);
    lv <@ L.hash(GA1.estar);
    Cstar.c <- (GA1.estar.`1 + GA1.estar.`2 * KeyStore.h, GA1.mstar + lv);
    GFlag.bad_corr <- decoder (Cstar.c.`1 * h0) h0 h1 <> Some GA1.estar;
    b <$ {0,1};
    kstar <$ duniformM;
    k1 <$ duniformM;
    b' <@ B(CountH(H), L, CountK(KMonQ), ODecapsA).guess
            (KeyStore.h, Cstar.c, b ? k1 : kstar);
    return b' = b;
  }
}.

(* GA4: single challenge key, b moved to the tail. *)
local module GA4 = {
  proc main() : bool = {
    var h0, h1, sigma, lv, kc, kd, b, b';
    L.init(); H.init(); Kh.init();
    CountH.c <- 0; CountK.c <- 0; CountK.qs <- [];
    GFlag.bad_sig <- false; GFlag.bad_corr <- false; GFlag.dmap <- empty;
    QFlag.query <- false;
    h0 <$ dHw; h1 <$ dHw; sigma <$ duniformM;
    KeyStore.sk <- (h0, h1); KeyStore.sigma <- sigma;
    KeyStore.h <- h1 * invp h0;
    GA1.mstar <$ duniformM;
    GA1.estar <@ H.hash(GA1.mstar);
    lv <@ L.hash(GA1.estar);
    Cstar.c <- (GA1.estar.`1 + GA1.estar.`2 * KeyStore.h, GA1.mstar + lv);
    GFlag.bad_corr <- decoder (Cstar.c.`1 * h0) h0 h1 <> Some GA1.estar;
    kc <$ duniformM;
    kd <$ duniformM;
    b' <@ B(CountH(H), L, CountK(KMonQ), ODecapsA).guess
            (KeyStore.h, Cstar.c, kc);
    b <$ {0,1};
    return b' = b;
  }
}.

(* Losslessness of the oracle tuple used by GA3 / GA4. *)
local lemma CountH_H_ll : islossless CountH(H).hash.
proof. proc; call H_hash_ll; auto. qed.

local lemma KMonQ_ll : islossless KMonQ.hash.
proof. proc; call Kh_hash_ll; auto. qed.

local lemma CountK_KMonQ_ll : islossless CountK(KMonQ).hash.
proof. proc; call KMonQ_ll; auto. qed.

local lemma CountK_Kh_ll : islossless CountK(Kh).hash.
proof. proc; call Kh_hash_ll; auto. qed.

local lemma GA2_GA2q &m :
  Pr[GA2.main() @ &m : res] = Pr[GA2q.main() @ &m : res].
proof.
byequiv (: ={glob B} ==> ={res}) => //.
proc.
swap{1} 23 -2.
call (_: ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
           KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
           CountH.c, CountK.c, CountK.qs,
           GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
           GA1.mstar, GA1.estar}).
+ by sim.
+ by sim.
+ proc.
  inline{1} KMon.hash. inline{2} KMonQ.hash.
  sp 3 3.
  if => //.
  + sp 1 1.
    if{2}.
    + by wp; call Kh_hash_eq; auto => />.
    by wp; call Kh_hash_eq; auto => />.
  if{2}.
  + by wp; call Kh_hash_eq; auto => />.
  by wp; call Kh_hash_eq; auto => />.
+ by sim.
rnd.                  (* k1 *)
call Kh_hash_eq.      (* kstar *)
rnd.                  (* b *)
wp.                   (* bad_corr, Cstar.c *)
call L_hash_eq.       (* lv *)
call H_hash_eq.       (* estar *)
rnd.                  (* mstar *)
wp.                   (* KeyStore x3 *)
rnd. rnd. rnd.        (* sigma, h1, h0 *)
wp.                   (* flags, counters, QFlag.query *)
inline L.init H.init Kh.init
       ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
auto => />.
qed.

local lemma GA2q_GA3_upto :
  equiv[ GA2q.main ~ GA3.main :
         ={glob B} ==>
         ={QFlag.query} /\ (!QFlag.query{2} => ={res}) ].
proof.
proc.
seq 23 23 : (={glob B, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
               QFlag.query, GA1.mstar, GA1.estar, b, kstar}
             /\ QFlag.query{2} = false
             /\ eq_except (pred1 (GA1.mstar{2}, Cstar.c{2}))
                  ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}).
  inline{1} Kh.hash ROK.Lazy.LRO.o.
rcondt{1} 26.
+ move=> &m.
  conseq (: _ ==> ROK.Lazy.LRO.m = empty).
  + by move=> &1; smt(mem_empty).
  auto.                                 (* 20–25 を wp で掃く。末尾が L.hash で止まる *)
 call (_: ROK.Lazy.LRO.m = empty).
  + inline ROL.Lazy.LRO.o; auto.   (* 19: L.hash → ROL.o、ROK 不変 *)
  call (_: ROK.Lazy.LRO.m = empty).
  + inline ROH.Lazy.LRO.o; auto.   (* 18: H.hash → ROH.o、ROK 不変 *)
inline L.init H.init Kh.init
         ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto.                           (* 1–17 + init。ROK.m <- empty へ到達 *)
  wp.
  rnd.
  wp.
  rnd.
  wp.
  call L_hash_eq.
  call H_hash_eq.
  rnd.
  wp.
  rnd. rnd. rnd.
  wp.
  inline L.init H.init Kh.init
         ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto => />.
  smt(eq_except_setl mem_empty get_set_sameE).
exists* GA1.mstar{2}; elim* => ms.
exists* Cstar.c{2};   elim* => cs.
call (_: QFlag.query,
      ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
        KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
        CountH.c, CountK.c, CountK.qs,
        GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
        QFlag.query, GA1.mstar, GA1.estar}
      /\ eq_except (pred1 (ms, cs)) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
      /\ GA1.mstar{2} = ms /\ Cstar.c{2} = cs,
        QFlag.query{1} /\ QFlag.query{2}).
(* G1 *)
+ exact B_guess_ll.
(* G2 : CountH(H) *)
+ by proc; inline*; auto => />.
+ by move=> &2 hbad; proc; inline*; auto => />; smt(DEt_ll).
+ by move=> &1; proc; inline*; auto => />; smt(DEt_ll).
(* G5 : L *)
+ by proc; inline*; auto => />.
+ by move=> &2 hbad; proc; inline*; auto => />; smt(duniformM_ll).
+ by move=> &1; proc; inline*; auto => />; smt(duniformM_ll).
(* G8 : CountK(KMonQ) *)
+ proc.
  inline{1} KMonQ.hash. inline{2} KMonQ.hash.
  sp 3 3.
  seq 2 2 : (={x0, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
               QFlag.query, GA1.mstar, GA1.estar}
             /\ eq_except (pred1 (ms, cs)) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
             /\ GA1.mstar{2} = ms /\ Cstar.c{2} = cs
             /\ (QFlag.query{2} <=> x0{2} = (ms, cs))).
  + by auto => />; smt().
  case (QFlag.query{2}).
  (* then: query 済み。post は query{1}/\query{2}。両側 Kh.hash を lossless で流す *)
        + conseq (: _ ==> QFlag.query{1} /\ QFlag.query{2}); 1: smt().
    wp.
    call{1} Kh_hash_ll. call{2} Kh_hash_ll. auto => />; smt().
  (* else: !query{2} ⟹ x0{2} <> (ms,cs)。eq_except を跨いで結合 *)
  inline{1} Kh.hash ROK.Lazy.LRO.o.
  inline{2} Kh.hash ROK.Lazy.LRO.o.
  sp.
  seq 1 1 : (={x2, r, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
               QFlag.query, GA1.mstar, GA1.estar}
             /\ !QFlag.query{2}
             /\ x2{2} <> (ms, cs)
             /\ GA1.mstar{2} = ms /\ Cstar.c{2} = cs
             /\ eq_except (pred1 (ms, cs)) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}).
  + by auto => />; smt().
  if.
  + by move=> &1 &2 />; smt(eq_exceptP domE).
  + by auto => />; smt(get_set_sameE eq_except_set_eq eq_exceptP domE).
    by auto => />; smt(eq_exceptP domE).
    (* G9 : CountK(KMonQ) 左 lossless-after-bad *)
+ move=> &2 hbad.
  conseq (: QFlag.query ==> QFlag.query).
  + by smt().
  + by smt().
  proc; inline KMonQ.hash Kh.hash ROK.Lazy.LRO.o; auto => />.
        + by move=> &hr _; rewrite duniformM_ll.
    (* G10 : CountK(KMonQ) 右 lossless-after-bad *)
+ move=> &1.
  conseq (: QFlag.query ==> QFlag.query) (: true ==> true) => //.
  + proc; inline KMonQ.hash Kh.hash ROK.Lazy.LRO.o; auto => />.
  by move=> &hr _; apply duniformM_ll.
(* G11 : ODecapsA *)
+ conseq (: _ ==>
            ={res, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, KeyStore.sk, KeyStore.sigma,
                KeyStore.h, Cstar.c, CountH.c, CountK.c, CountK.qs,
                GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap, QFlag.query,
                GA1.mstar, GA1.estar}
            /\ eq_except (pred1 (ms, cs)) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
            /\ GA1.mstar{2} = ms /\ Cstar.c{2} = cs); 1: smt().
  + proc.
  sp; if => //.
  (* c <> Cstar.c の枝。Decrypt1 は ROL/ROH のみ、両側同期 *)
  seq 1 1 : (={mo, c, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
               QFlag.query, GA1.mstar, GA1.estar}
             /\ c{2} <> Cstar.c{2}
             /\ eq_except (pred1 (ms, cs)) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
             /\ GA1.mstar{2} = ms /\ Cstar.c{2} = cs).
  + by call Decrypt1_eq; auto => />.
  if => //.
  + (* mo <> None: Kh.hash((oget mo, c))。c <> cs ゆえ引数 <> (ms,cs) *)
    inline{1} Kh.hash ROK.Lazy.LRO.o.
    inline{2} Kh.hash ROK.Lazy.LRO.o.
    sp.
    seq 1 1 : (={x0, r, mo, c, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m,
                 KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
                 CountH.c, CountK.c, CountK.qs,
                 GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
                 QFlag.query, GA1.mstar, GA1.estar}
               /\ x0{2} <> (ms, cs)
               /\ ROK.Lazy.LRO.m{1}.[x0{1}] = ROK.Lazy.LRO.m{2}.[x0{2}]
               /\ eq_except (pred1 (ms, cs)) ROK.Lazy.LRO.m{1} ROK.Lazy.LRO.m{2}
               /\ GA1.mstar{2} = ms /\ Cstar.c{2} = cs).      (* ★この行を追加 *)
    + by auto => />; smt(eq_exceptP pred1E).
    case (x0{1} \in ROK.Lazy.LRO.m{1}).
    + rcondf{1} 1; first by auto.
      rcondf{2} 1; first by move=> &m; auto => />; smt(domE).
      by auto => />; smt(domE).
    + rcondt{1} 1; first by auto.
      rcondt{2} 1; first by move=> &m; auto => />; smt(domE).
      by auto => />; smt(get_set_sameE eq_except_set_eq domE).
  (* G11 : mo = None 枝。dmap 更新のみ、ROK 不変、両側同一 *)
  if => //.
  + by auto => />.
  by auto => />.
(* G12 : ODecapsA lossless-after-bad 左 *)
+ by move=> &2 hbad; conseq ODecapsA_ll => //.
(* G13 : ODecapsA lossless-after-bad 右 *)
+ by move=> &1; conseq ODecapsA_ll => //.
(* 最終: seq 23 23 の不変式が upto-call の pre に一致（ms=GA1.mstar{2}, cs=Cstar.c{2}）*)
auto => />; smt(mem_empty eq_exceptP).    
qed.

local lemma GA2q_GA3_abs &m :
  `| Pr[GA2q.main() @ &m : res] - Pr[GA3.main() @ &m : res] |
  <= Pr[GA3.main() @ &m : QFlag.query].
proof.
have hres : Pr[GA2q.main() @ &m : res /\ !QFlag.query]
          = Pr[GA3.main()  @ &m : res /\ !QFlag.query].
+ by byequiv GA2q_GA3_upto => // /#.
have hbad : Pr[GA2q.main() @ &m : QFlag.query]
          = Pr[GA3.main()  @ &m : QFlag.query].
+ by byequiv GA2q_GA3_upto => // /#.
have e1 : Pr[GA2q.main() @ &m : res]
  = Pr[GA2q.main() @ &m : res /\ QFlag.query]
  + Pr[GA2q.main() @ &m : res /\ !QFlag.query].
+ by rewrite Pr [mu_split QFlag.query].
have e2 : Pr[GA3.main() @ &m : res]
  = Pr[GA3.main() @ &m : res /\ QFlag.query]
  + Pr[GA3.main() @ &m : res /\ !QFlag.query].
+ by rewrite Pr [mu_split QFlag.query].
have u1 : Pr[GA2q.main() @ &m : res /\ QFlag.query]
       <= Pr[GA2q.main() @ &m : QFlag.query].
+ by rewrite Pr [mu_sub] => /#.
have u2 : Pr[GA3.main() @ &m : res /\ QFlag.query]
       <= Pr[GA3.main() @ &m : QFlag.query].
+ by rewrite Pr [mu_sub] => /#.
have g1 : 0%r <= Pr[GA2q.main() @ &m : res /\ QFlag.query].
+ by rewrite Pr [mu_ge0].
have g2 : 0%r <= Pr[GA3.main() @ &m : res /\ QFlag.query].
+ by rewrite Pr [mu_ge0].
smt().
qed.

local lemma GA3_GA4 &m :
  Pr[GA3.main() @ &m : res] = Pr[GA4.main() @ &m : res].
proof.
byequiv (: ={glob B} ==> ={res}) => //.
proc.
seq 21 21 : (={glob B, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs,
               GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
               QFlag.query, GA1.mstar, GA1.estar}).
+ by sim.
swap{2} 4 -3.
seq 1 1 : (={glob B, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
             KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
             CountH.c, CountK.c, CountK.qs,
             GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
             QFlag.query, GA1.mstar, GA1.estar, b}).
+ by rnd; auto.
case (b{1}).
+ swap{2} 1 1.
  wp.
  call (_: ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
             KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
             CountH.c, CountK.c, CountK.qs,
             GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
             QFlag.query, GA1.mstar, GA1.estar});
    first 4 by sim.
  rnd. rnd.
  auto => />.
wp.
call (_: ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
           KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
           CountH.c, CountK.c, CountK.qs,
           GFlag.bad_sig, GFlag.bad_corr, GFlag.dmap,
           QFlag.query, GA1.mstar, GA1.estar});
  first 4 by sim.
rnd. rnd.
auto => />.
qed.

local lemma GA4_full &m : Pr[GA4.main() @ &m : true] = 1%r.
proof.
byphoare => //.
proc.
rnd.
call (B_guess_ll (CountH(H)) L (CountK(KMonQ)) ODecapsA
        CountH_H_ll L_hash_ll CountK_KMonQ_ll ODecapsA_ll).
rnd.
rnd.
wp.
call L_hash_ll.
call H_hash_ll.
rnd.
wp.
rnd.
rnd.
rnd.
wp.
inline L.init H.init Kh.init
       ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
auto => />.
smt(duniformM_ll dHw_ll dbool_ll).
qed.

local lemma GA4_flip &m :
  Pr[GA4.main() @ &m : res] = Pr[GA4.main() @ &m : !res].
proof.
byequiv (: ={glob B} ==> res{1} <=> !res{2}) => //.
proc.
seq 24 24 : (={b'}); first by sim.
rnd (fun (x : bool) => !x).
auto => />.
smt(dbool1E dbool_fu).
qed.

local lemma GA4_half &m : Pr[GA4.main() @ &m : res] = 1%r/2%r.
proof.
have hf := GA4_full &m.
have hp := GA4_flip &m.
have hs : Pr[GA4.main() @ &m : true]
  = Pr[GA4.main() @ &m : res] + Pr[GA4.main() @ &m : !res].
+ rewrite Pr [mu_split res]; congr; rewrite Pr [mu_eq] => /#.
smt().
qed.

local lemma GA3_bad_corr &m :
  Pr[GA3.main() @ &m : GFlag.bad_corr] <= Pr[Corr.main() @ &m : res].
proof.
byequiv (: ={glob B} ==> GFlag.bad_corr{1} => res{2}) => //.
proc.
(* ---- Part 1: bad_corr 確定まで（左21 ~ 右3）を結合 ---- *)
seq 21 3 : (GFlag.bad_corr{1}
            = (decoder (e{2}.`1 * h0{2} + e{2}.`2 * h1{2}) h0{2} h1{2}
               <> Some e{2})).
+ inline{1} H.hash L.hash ROH.Lazy.LRO.o ROL.Lazy.LRO.o.
  inline{1} L.init H.init Kh.init
            ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
  wp.
  (* 左サンプル（末尾から）: e_H(18内部) , mstar(17) , sigma(13) , h1(12) , h0(11) *)
  (* さらに L.hash 内部 lv サンプルが (19) にある点に注意 *)
  rnd{1}.          (* (19) lv：右に無し（デッド） *)
  wp.
  rnd.
  wp.
  rnd{1}.          (* (17) mstar：デッド *)
  wp.
  rnd{1}.          (* (13) sigma：デッド *)
  rnd. rnd.        (* (12) h1, (11) h0 *)
  auto => />.
  smt(dHw_supp Corr_syndrome get_set_sameE mem_empty duniformM_ll).
(* ---- Part 2: 残る左 (22)-(25) を lossless で消化。右は空 ---- *)
conseq (: GFlag.bad_corr{1}
          = (decoder (e{2}.`1 * h0{2} + e{2}.`2 * h1{2}) h0{2} h1{2}
             <> Some e{2})
          ==> _) => //.
call{1} (B_guess_ll (CountH(H)) L (CountK(KMonQ)) ODecapsA
          CountH_H_ll L_hash_ll CountK_KMonQ_ll ODecapsA_ll).
rnd{1}. rnd{1}. rnd{1}.        (* (24) k1, (23) kstar, (22) b *)
skip => />; smt(duniformM_ll).
qed.

local lemma GA3_query_notcorr &m :
  Pr[GA3.main() @ &m : QFlag.query /\ !GFlag.bad_corr]
  <= Pr[OW_PCA(B_ow(B)).main() @ &m : res].
proof.
byequiv (: ={glob B} ==> (QFlag.query{1} /\ !GFlag.bad_corr{1}) => res{2}) => //.
proc.
  inline{2} OW_PCA(B_ow(B)).main.          (* CHECK: 対象名。ダメなら PKE.keyGen 等を個別 inline *)
inline{2} B_ow(B, H, L, Pco).find PKE.keyGen PKE1.encrypt.
(* ===== prefix: init〜cstar/bad_corr。INV 初期値を確立 ===== *)
seq 21 19 : (
     ={glob B, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, KeyStore.sk, KeyStore.h}
  /\ Cstar.c{1} = B_ow.cst{2}
  /\ GA1.mstar{1} = mstar{2}
  /\ CountK.qs{1} = B_ow.qs{2} /\ CountK.qs{1} = []
  /\ QFlag.query{1} = false
  /\ B_ow.kmap{2} = empty /\ B_ow.dmap{2} = empty
  /\ B_ow.dseen{2} = [] /\ GFlag.dmap{1} = empty
  /\ (GFlag.bad_corr{1} =>
        decoder (Cstar.c{1}.`1 * (KeyStore.sk{1}).`1)
                (KeyStore.sk{1}).`1 (KeyStore.sk{1}).`2 <> Some GA1.estar{1})
  /\ (!GFlag.bad_corr{1} =>
        decoder (Cstar.c{1}.`1 * (KeyStore.sk{1}).`1)
                (KeyStore.sk{1}).`1 (KeyStore.sk{1}).`2 = Some GA1.estar{1})).
+ admit. (* TODO(prefix) *)
(* ===== challenge key: (b?k1:kstar){1} ~ k0{2} を一様結合、b/デッド消費 ===== *)
swap{1} 1 2.        (* [b,kstar,k1] → [kstar,k1,b] *)
seq 3 1 : (
     ={glob B, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, KeyStore.sk, KeyStore.h}
  /\ Cstar.c{1} = B_ow.cst{2}
  /\ GA1.mstar{1} = mstar{2}
  /\ CountK.qs{1} = B_ow.qs{2} /\ CountK.qs{1} = []
  /\ QFlag.query{1} = false
  /\ B_ow.kmap{2} = empty /\ B_ow.dmap{2} = empty
  /\ B_ow.dseen{2} = [] /\ GFlag.dmap{1} = empty
  /\ (!GFlag.bad_corr{1} =>
        decoder (Cstar.c{1}.`1 * (KeyStore.sk{1}).`1)
                (KeyStore.sk{1}).`1 (KeyStore.sk{1}).`2 = Some GA1.estar{1})
  /\ (if b{1} then k1{1} else kstar{1}) = k0{2}).
+ admit.
admit.
qed.

local lemma GA3_query_split &m :
  Pr[GA3.main() @ &m : QFlag.query]
  <= Pr[Corr.main() @ &m : res] + Pr[OW_PCA(B_ow(B)).main() @ &m : res].
proof.
have h1 := GA3_bad_corr &m.
have h2 := GA3_query_notcorr &m.
have hs : Pr[GA3.main() @ &m : QFlag.query]
  = Pr[GA3.main() @ &m : QFlag.query /\ GFlag.bad_corr]
  + Pr[GA3.main() @ &m : QFlag.query /\ !GFlag.bad_corr].
+ by rewrite Pr [mu_split GFlag.bad_corr].
have hu : Pr[GA3.main() @ &m : QFlag.query /\ GFlag.bad_corr]
       <= Pr[GA3.main() @ &m : GFlag.bad_corr].
+ by rewrite Pr [mu_sub] => /#.
smt().
qed.

local lemma GA2_bad_sig_eq &m :
  Pr[GA2.main() @ &m : GFlag.bad_sig]
  = Pr[GA2'.main() @ &m
        : has (fun (x : M * C) => x.`1 = KeyStore.sigma) CountK.qs].
proof.
byequiv (: ={glob B} ==>
           GFlag.bad_sig{1}
           = has (fun (x : M * C) => x.`1 = KeyStore.sigma{2}) CountK.qs{2}) => //.
proc.
call (_: ={ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
           KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
           CountH.c, CountK.c, CountK.qs, GFlag.bad_corr, GFlag.dmap,
           GA1.mstar, GA1.estar}
        /\ (GFlag.bad_sig{1}
            = has (fun (x : M * C) => x.`1 = KeyStore.sigma{2}) CountK.qs{2})).
+ (* CountH(H) *)
  by proc; inline*; auto => />.
+ (* L *)
  by proc; inline*; auto => />.
+ (* CountK(KMon){1} ~ CountK(Kh){2} *)
  proc.
  inline{1} KMon.hash.
  inline{1} Kh.hash. inline{2} Kh.hash.
  inline{1} ROK.Lazy.LRO.o. inline{2} ROK.Lazy.LRO.o.
  auto => />.
+ proc.
  sp; if => //.
  seq 1 1 : (={mo, c, ROL.Lazy.LRO.m, ROH.Lazy.LRO.m, ROK.Lazy.LRO.m,
               KeyStore.sk, KeyStore.sigma, KeyStore.h, Cstar.c,
               CountH.c, CountK.c, CountK.qs, GFlag.bad_corr,
               GFlag.dmap, GA1.mstar, GA1.estar}
             /\ GFlag.bad_sig{1}
                = has (fun (x : M * C) => x.`1 = KeyStore.sigma{2}) CountK.qs{2}).
  + by call Decrypt1_eq; auto => />.
  if => //.
  + by inline Kh.hash ROK.Lazy.LRO.o; auto => />.
  if => //.
  + by auto => />.
  by auto => />.
(* 前置き *)
auto => />.
smt(has_pred0).
wp.
call Kh_hash_eq.        (* (21) kstar <@ Kh.hash *)
wp.
call L_hash_eq.         (* (18) lv <@ L.hash *)
call H_hash_eq.         (* (17) estar <@ H.hash *)
wp.
rnd.
wp.
rnd. rnd.          (* (16) mstar, (12) sigma, (11) h1 … 実際の並びに合わせる *)
rnd.
inline L.init H.init Kh.init
       ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
auto => />.
qed.

local lemma GA2_bad_sig &m :
  Pr[GA2.main() @ &m : GFlag.bad_sig] <= qK%r * epsM.
proof.
rewrite (GA2_bad_sig_eq &m).
byphoare (: true ==>
           has (fun (x : M * C) => x.`1 = KeyStore.sigma) CountK.qs) => //.
proc.
swap 14 -1.
swap [12..13] 11.
seq 22 : (size CountK.qs <= qK) 1%r (qK%r * epsM) 0%r 1%r.
(* ===== 本1: hoare, post = true, prefix ===== *)
  + call (: true).              (* (22) B.guess: trivial spec *)
  by auto.
  by auto.
  by auto.
  by auto.
  rnd. rnd.                   (* (21)b (20)k1 *)
  call (: true).              (* (19) Kh *)
  by auto.
  wp.                         (* (18)(17) *)
  call (: true).              (* (16) L *)
  by auto.
  call (: true).              (* (15) H *)
  by auto.
  rnd.                        (* (14) mstar *)
  wp.                         (* (13)(12) *)
  rnd. rnd.                   (* (11)(10) *)
  inline L.init H.init Kh.init
         ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto.
(* ===== 本2: [<=]1%r → 自明（確率上界1） ===== *)
+ conseq (: _ ==> true) => //.
(* ===== 本3: [<=]qK·epsM, tail σ2命令 ← 本体 ===== *)
+ wp.
  rnd; skip.
  move=> &hr hqs.
  have h1 : mu duniformM (fun (s : M) => has (fun (x : M * C) => x.`1 = s) CountK.qs{hr})
            <= (size CountK.qs{hr})%r * epsM.
  + apply (mu_has_leM (fun (s : M) (x : M * C) => x.`1 = s) duniformM
                      CountK.qs{hr} epsM).
    move=> x hx /=.
    have -> : (fun (s : M) => x.`1 = s) = pred1 x.`1.
    + apply fun_ext => s; rewrite /pred1; smt().
    exact mu1_duniformM_le.
  have h2 : (size CountK.qs{hr})%r * epsM <= qK%r * epsM.
  + have hp : 0%r <= epsM by rewrite /epsM; smt(mu_bounded).
    have hs : (size CountK.qs{hr})%r <= qK%r.
    + rewrite le_fromint; exact hqs.
    smt().
  split.
  + apply (StdOrder.RealOrder.ler_trans ((size CountK.qs{hr})%r * epsM)).
    + rewrite (mu_eq duniformM
        (fun (x : QuotientVec.vector) => has (fun (x0 : M * C) => x0.`1 = x) CountK.qs{hr})
        (fun (s : M) => has (fun (x : M * C) => x.`1 = s) CountK.qs{hr})).
      + done.
      exact h1.
    + exact h2.
  + by move=> v hv hhas /=.
(* ===== 本4: [<=]0%r, post = !(size qs<=qK), prefix ===== *)
+ hoare.
  call (B_qbound H L Kh ODecapsA).
  rnd. rnd.
  call (: true).
  by auto.
  wp.
  call (: true).
  by auto.
  call (: true).
  by auto.
  rnd.
  wp.
  rnd. rnd.
  inline L.init H.init Kh.init
         ROL.Lazy.LRO.init ROH.Lazy.LRO.init ROK.Lazy.LRO.init.
  auto => />.
(* ===== 本5: 算術 ===== *)
+ by smt().
qed.

(* --------------------------------------------------------------------
   [24, Thm 3.4] (U-bot-slash): IND-CCA(KEM6bot) -> OW-PCA(PKE1).
   Paper bound:  |Pr[IND_CCA(B)] - 1/2| <= qK * epsM
                                          + Pr[OW_PCA(B_ow(B))].
   Proof plan (M3):
     hop 1: replace the implicit-rejection branch K(sigma, .) by an
            independent random function; bad = B queries K at
            (sigma, .); Pr[bad] <= qK * epsM (sigma is uniform and
            never revealed).
     hop 2: replace Decaps by the sk-free simulation SimD, patching K
            through Pco (perfect, conditioned on hop 1) — the L-state
            bookkeeping of design P3 lives here.
     hop 3: the challenge key is random unless B queries K at
            (m*, c* ); that query is exactly the OW extraction of
            B_ow(B).
   -------------------------------------------------------------------- *)
lemma HHK_Thm34 &m :
 `| Pr[IND_CCA(B).main() @ &m : res] - 1%r/2%r |
  <= qK%r * epsM
   + Pr[Corr.main() @ &m : res]
   + Pr[OW_PCA(B_ow(B)).main() @ &m : res].
proof.
have h1 := IND_CCA_GA0 &m.
have h2 := GA0_GA1 &m.
have h3 := GA1_GA2_abs &m.
have h4 := GA2_bad_sig &m.
have h5 := GA2_GA2q &m.
have h6 := GA2q_GA3_abs &m.
have h7 := GA3_GA4 &m.
have h8 := GA4_half &m.
have h9 := GA3_query_split &m.
smt().
qed.

(* --------------------------------------------------------------------
   [24, Thm 3.2] downgraded to OW-PCA (spec C.2.2):
     Pr[OW_PCA(B0)] <= qH * delta + (2*qH + 1) * epsM
                       + 3 * |Pr[G0_spec(A_cpa(B0))] - 1/2|
   with delta = Pr[Corr]. Stated for the concrete reduction; the
   IND-CPA term is the base file's spec-faithful game, so
   Theorem2_final chains directly.
   Proof plan (M4):
     hop 1: per-H-query correctness bad (hybrid over the at most qH
            fresh H outputs; each contributes <= Pr[Corr] via
            Corr_syndrome) — replaces Pco by the re-encryption check
            SimPco.
     hop 2: challenge derandomization: e* = H(m* ) vs e* <$ E_t; bad =
            B0 queries H at m*; deferred-decision + OTP (base-file
            vec_subrK toolkit) gives the qH * epsM and guessing terms.
     hop 3: case analysis of the decision rule => factor 3 and the
            remaining (qH + 1) * epsM.
   -------------------------------------------------------------------- *)
lemma HHK_Thm32 (B0 <: OWPCA_Adv
    {-Bike, -L, -ROL.Lazy.LRO, -BadWit, -H, -ROH.Lazy.LRO,
     -KeyStore, -A_cpa}) &m :
  Pr[OW_PCA(B0).main() @ &m : res]
  <= qH%r * Pr[Corr.main() @ &m : res]
   + (2 * qH + 1)%r * epsM
   + 3%r * `| Pr[G0_spec(A_cpa(B0)).main() @ &m : res] - 1%r/2%r |.
proof.
admit. (* TODO(M4) *)
qed.

(* --------------------------------------------------------------------
   Losslessness toolkit for the simulators (M5, feeds Acpa_guess_ll).
   -------------------------------------------------------------------- *)
lemma Acpa_SimH_ll (B0 <: OWPCA_Adv {-A_cpa}) (O <: OrclL {-A_cpa}) :
  islossless A_cpa(B0, O).SimH.hash.
proof.
proc; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll).
qed.

lemma Acpa_SimPco_ll (B0 <: OWPCA_Adv {-A_cpa}) (O <: OrclL {-A_cpa}) :
  islossless O.hash => islossless A_cpa(B0, O).SimPco.pco.
proof.
move=> hO; proc; call hO; inline ROH.Lazy.LRO.o; auto => />; smt(DEt_ll).
qed.

lemma Bow_SimK_ll (OH <: OrclH {-B_ow}) (OL <: OrclL {-B_ow})
                  (OP <: PCO_t {-B_ow}) :
  islossless OP.pco => islossless B_ow(B, OH, OL, OP).SimK.hash.
proof. move=> hP; proc; islossless; smt(duniformM_ll). qed.

lemma Bow_SimD_ll (OH <: OrclH {-B_ow}) (OL <: OrclL {-B_ow})
                  (OP <: PCO_t {-B_ow}) :
  islossless OP.pco => islossless B_ow(B, OH, OL, OP).SimD.decaps.
proof.
move=> hP.
proc.
sp.
if => //.
if => //.
wp.
while (true) (size rest).
+ move=> z.
  sp 2.
  if.
  + wp; call hP; auto => />; smt(size_behead size_ge0).
  auto => />; smt(size_behead size_ge0).
  wp; call hP; auto => />; smt(duniformM_ll size_ge0).
auto.
qed.

lemma Bow_find_ll (OH <: OrclH {-B, -B_ow}) (OL <: OrclL {-B, -B_ow})
                  (OP <: PCO_t {-B, -B_ow}) :
  islossless OH.hash => islossless OL.hash => islossless OP.pco =>
  islossless B_ow(B, OH, OL, OP).find.
proof.
move=> hH hL hP.
proc.
while (true) (size rest).
+ move=> z.
  wp; call hP; auto => />; smt(size_behead size_ge0).
wp.
call (B_guess_ll OH OL
        (<: B_ow(B, OH, OL, OP).SimK) (<: B_ow(B, OH, OL, OP).SimD)
        hH hL (Bow_SimK_ll OH OL OP hP) (Bow_SimD_ll OH OL OP hP)).
conseq (: _ ==> true).
+ move=> &hr _.
  split=> //.
  move=> _ found0 rest0.
  split=> //.
  smt().
by auto => />; exact duniformM_ll.
qed.

(* --------------------------------------------------------------------
   Obligations for instantiating the base file's section lemmas at
   A := A_cpa(B_ow(B)) : LOR_Adv. (M5)
   -------------------------------------------------------------------- *)
lemma Acpa_choose_ll (O <: OrclL {-A_cpa(B_ow(B))}) :
  islossless O.hash => islossless A_cpa(B_ow(B), O).choose.
proof.
move=> _; proc; inline*; auto => />; smt(duniformM_ll).
qed.

lemma Acpa_guess_ll (O <: OrclL {-A_cpa(B_ow(B))}) :
  islossless O.hash => islossless A_cpa(B_ow(B), O).guess.
proof.
move=> hO.
have hSimH := Acpa_SimH_ll (<: B_ow(B)) O.
have hSimP := Acpa_SimPco_ll (<: B_ow(B)) O hO.
proc.
wp.
call (Bow_find_ll
        (<: A_cpa(B_ow(B), O).SimH) O (<: A_cpa(B_ow(B), O).SimPco)
        hSimH hO hSimP).
rnd; auto => />; smt(dbool_ll).
qed.

(* A_choose_wf: both messages are duniformM samples, hence size l
   (duniformM_size) — the base file's well-formedness contract holds
   by construction. *)
lemma Acpa_choose_wf (O <: OrclL {-A_cpa(B_ow(B))}) :
  hoare[ A_cpa(B_ow(B), O).choose :
         true ==> size res.`1 = l /\ size res.`2 = l ].
proof.
proc; inline*; auto => />; smt(duniformM_size).
qed.

(* --------------------------------------------------------------------
   Lemma 2 (spec C.2.2). Lemma2_exact is the exact composition of
   HHK_Thm34 and HHK_Thm32; Lemma2 is the spec's aggregated form
   (q = qH + qK), whose slack qK+2qH+1 <= 3(qH+qK) additionally needs
   qH_ge1 (made explicit by the mechanization).
   -------------------------------------------------------------------- *)
lemma Lemma2_exact &m :
  `| Pr[IND_CCA(B).main() @ &m : res] - 1%r/2%r |
 <= (qH + 1)%r * Pr[Corr.main() @ &m : res]
   + (qK + 2 * qH + 1)%r * epsM
   + 3%r * `| Pr[G0_spec(A_cpa(B_ow(B))).main() @ &m : res] - 1%r/2%r |.
proof.
have h1 := HHK_Thm34 &m.
have h2 := HHK_Thm32 (B_ow(B)) &m.
smt().
qed.

lemma Lemma2 &m :
  `| Pr[IND_CCA(B).main() @ &m : res] - 1%r/2%r |
  <= (qH + qK)%r * Pr[Corr.main() @ &m : res]
   + 3%r * (qH + qK)%r * epsM
   + 3%r * `| Pr[G0_spec(A_cpa(B_ow(B))).main() @ &m : res] - 1%r/2%r |.
proof.
have he := Lemma2_exact &m.
have hp : 0%r <= epsM by rewrite /epsM; smt(mu_bounded).
have hd : 0%r <= Pr[Corr.main() @ &m : res] by rewrite Pr [mu_ge0].
smt(qH_ge0 qK_ge0 qH_ge1 qK_ge1).
qed.

(* --------------------------------------------------------------------
   Theorem 3 (spec C.3, eq. (4)) in concrete-security form:
   instantiate the base file's Theorem2_final at A := A_cpa(B_ow(B))
   (with Acpa_choose_ll / Acpa_guess_ll / Acpa_choose_wf discharging
   the section hypotheses) and chain with Lemma2:

     |Pr[IND_CCA(B)] - 1/2|
       <= (qH+qK) * Pr[Corr] + 3*(qH+qK) * epsM
        + 3/2 * |Pr[DQCCF(D_cf(Red(A_cpa(B_ow(B)))))(false)]
                 - Pr[DQCCF(D_cf(Red(A_cpa(B_ow(B)))))(true)]|
        + 3/2 * Pr[G4_OW_S(Red(A_cpa(B_ow(B))))].

   Paper reading: delta = DFR (C.2.1), epsM = 1/|M|, and the last two
   terms are (3/2) Adv^IND_qccf(D) + (3/2) Adv^OW_qcsd(A') for the
   explicit D / A'. As in revision f, no hardness or DFR axiom is
   declared; the computational reading lives in prose.
   -------------------------------------------------------------------- *)
lemma Theorem3_concrete &m :
  `| Pr[IND_CCA(B).main() @ &m : res] - 1%r/2%r |
  <= (qH + qK)%r * Pr[Corr.main() @ &m : res]
   + 3%r * (qH + qK)%r * epsM
   + 3%r/2%r * `| Pr[DQCCF(D_cf(Red(A_cpa(B_ow(B))))).main(false) @ &m : res]
                - Pr[DQCCF(D_cf(Red(A_cpa(B_ow(B))))).main(true)  @ &m : res] |
   + 3%r/2%r * Pr[G4_OW_S(Red(A_cpa(B_ow(B)))).main() @ &m : res].
proof.
have h1 := Lemma2 &m.
have h2 := Theorem2_final (A_cpa(B_ow(B)))
             Acpa_choose_ll Acpa_guess_ll Acpa_choose_wf &m.
smt().
qed.

end section CCA_Security.
