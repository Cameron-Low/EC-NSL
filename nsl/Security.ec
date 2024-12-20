require import AllCore FSet FMap List Distr DProd PROM NSL Games.
import GWAKEc AEADc PRFc.
require Birthday.

lemma negb_exists2 (P : 'a -> 'b -> bool) : ! (exists x y, P x y) <=> (forall x y, ! P x y).
proof.
smt().
qed.
 
(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

(* AEAD Reduction *)
module (Red_AEAD (D : A_GWAKE) : A_GAEAD) (O : GAEAD_out) = {
  module WAKE_O : GWAKE_out = {
    var state_map: (id * int, role * instance_state) fmap
  
    proc init_mem() : unit = {
      state_map <- empty;
    }
  
    proc gen_pskey = O.gen
  
    proc send_msg1(a, i, b) = {
      var ex, na;
      var mo <- None;
  
      ex <@ O.ex((a, b));
      if ((a, i) \notin state_map /\ ex) {
        na <$ dnonce;
        mo <@ O.enc((a, b), msg1_data a b, na);
        state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, oget mo) (a, oget mo));
      }
      return mo;
    }

    proc send_msg2(b, j, m1) = {
      var a, ca, role, st, ex, n, nb;
      var mo <- None;
  
      (a, ca) <- m1;
      (role, st) <- oget state_map.[(b, j)];
      ex <@ O.ex((a, b));
      if ((b, j) \notin state_map /\ ex) {
        n <@ O.dec((a, b), msg1_data a b, ca);
        if (n is Some na) {
          nb <$ dnonce;
          mo <@ O.enc((a, b), msg2_data a b ca, nb);
          state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, oget mo) m1 (oget mo));
        } else {
          state_map.[(b, j)] <- (Responder, Aborted);
        }
      }
      return mo;
    }

    proc send_msg3(a, i, m2) = {
      var role, st, b, psk, na, ca, n, skey, ok;
      var mo <- None;
  
      if ((a, i) \in state_map) {
        (role, st) <- oget state_map.[(a, i)];
        if (st is IPending s m1) {
          (b, psk, na, ca) <- s;
          n <@ O.dec((a, b), msg2_data a b ca, m2);
          if (n is Some nb) {
            skey <- prf (na, nb) (a, b);
            ok <$ dnonce;
            mo <@ O.enc((a, b), msg3_data a b ca m2, ok);
            state_map.[(a, i)] <- (Initiator, Accepted ((a, ca), m2, oget mo) skey);
          } else {
            state_map.[(a, i)] <- (Initiator, Aborted);
          }
        }
      }
      return mo;
    }

    proc send_fin(b, j, m3) = {
      var role, st, a, psk, na, nb, ca, cb, ok, skey;
      var mo <- None;

      if ((b, j) \in state_map) {
        (role, st) <- oget state_map.[(b, j)];
        if (st is RPending s m1 m2) {
          (a, psk, na, nb, ca, cb) <- s;
          ok <@ O.dec((a, b), msg3_data a b ca cb, m3);
          if (ok is Some nok) {
            skey <- prf (na, nb) (a, b);
            state_map.[(b, j)] <- (Responder, Accepted ((a, ca), cb, m3) skey);
            mo <- Some ();
          } else {
            state_map.[(b, j)] <- (Responder, Aborted);
          }
        }
      }
      return mo;
    }

    proc rev_skey(a, i) = {
      var role, st, p_role, p_st, ps, p, k;
      var ko <- None;
  
      if ((a, i) \in state_map) {
        (role, st) <- oget state_map.[(a, i)];
        match st with
        | Accepted trace k' => {
          k <- k';
          ps <- get_partners (a, i) (Some trace) role state_map;
          if (card ps <= 1) {
            ps <- get_observed_partners (a, i) state_map;
            if (card ps <> 0) {
              p <- pick ps;
              (p_role, p_st) <- oget state_map.[p];
              if (p_st is Observed _ p_k) {
                k <- p_k;
              }
            }
            ko <- Some k;
            state_map.[(a, i)] <- (role, Observed trace k);
          }
        }
        | Observed _ k'  => ko <- Some k';
        | IPending _ _   => { }
        | RPending _ _ _ => { }
        | Aborted        => { }
        end;
      }
      return ko;
    }
  
    proc test = rev_skey
  }
  
  proc run() = {
    var b;
    WAKE_O.init_mem();
    b <@ D(WAKE_O).run();
    return b;
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* ROM Reduction *)

clone import PROM.FullRO as NROc with
  type in_t    <= msg_data * ctxt,
  type out_t   <= nonce,
  op   dout  _ <= dnonce,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

module (Red_ROM (D : A_GWAKE) : RO_Distinguisher) (O : RO) = {
  module WAKE_O : GWAKE_out = Game4 with {
    proc send_msg1 [
      ^if.^if.^na<$ ~ {na <- witness; O.sample((msg1_data a b, ca)); }
    ]

    proc send_msg2 [
      ^if.^match#Some.^if.^nb<$ ~ {nb <- witness; O.sample((msg2_data a b ca, cb)); }
    ]

    proc send_msg3 [
      ^if.^match#IPending.^match#Some.^if.^ok<$ ~ {
        ok <- witness;
        O.sample((msg3_data a b ca m2, caf));
      }
      ^if.^match#IPending.^match#Some.^if.^skey<- ~ {
        na <@ O.get((msg1_data a b, ca));
        ok <@ O.get((msg2_data a b ca, m2));
        skey <- prf (na, ok) (a, b);
      }
    ]

    proc send_fin [
      ^if.^match#RPending.^match#Some.^skey<- ~ {
        na <@ O.get((msg1_data a b, ca));
        nb <@ O.get((msg2_data a b ca, cb));
        skey <- prf (na, nb) (a, b);
      }
    ]
  }

  proc distinguish() = {
    var b;
    WAKE_O.init_mem();
    b <@ D(WAKE_O).run();
    return b;
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* PRF Reduction *)
module (Red_PRF (D : A_GWAKE) : A_GPRF) (O : GPRF_out) = {
  module WAKE_O : GWAKE_out = {
    var dec_map : ((id * id) * msg_data * ctxt, nonce) fmap
    var bad : bool
    var state_map : (id * int, role * instance_state) fmap
    var psk_map : (id * id, pskey) fmap
  
    proc init_mem() = {
      state_map <- empty;
      psk_map <- empty;
      bad <- false;
      dec_map <- empty;
    }
  
    proc gen_pskey(a, b) = {
      var k;
  
      if ((a, b) \notin psk_map) {
        k <$ dpskey;
        psk_map.[a, b] <- k;
      }
    }
  
    proc send_msg1(a, i, b) = {
      var ca, mo;
      
      mo <- None;
      if (((a, i) \notin state_map) /\ ((a, b) \in psk_map)) {
        ca <$ dctxt;
        bad <- bad \/ exists pk ad, (pk, ad, ca) \in dec_map;
        if (!bad) {
          dec_map.[(a, b), msg1_data a b, ca] <- witness;
          mo <- Some ca;
          state_map.[a, i] <- (Initiator, IPending (b, witness, witness, ca) (a, ca));
        }
      }
      
      return mo;
    }

    proc send_msg2(b : id, j : int, m1 : id * ctxt) : ctxt option = {
      var a, ca, role, st, cb, mo;
      
      mo <- None;
      (a, ca) <- m1;
      (role, st) <- oget state_map.[b, j];
      if (((b, j) \notin state_map) /\ ((a, b) \in psk_map)) {
        if (dec_map.[(a, b), msg1_data a b, ca] is Some na) {
          cb <$ dctxt;
          bad <- bad \/ exists pk ad, (pk, ad, cb) \in dec_map;
          if (!bad) {
            dec_map.[(a, b), msg2_data a b ca, cb] <- witness;
            mo <- Some cb;
            state_map.[b, j] <- (Responder, RPending (a, witness, witness, witness, ca, cb) m1 cb);
          }
        } else {
          state_map.[b, j] <- (Responder, Aborted);
        }
      }
      
      return mo;
    }
    
    proc send_msg3(a : id, i : int, m2 : ctxt) : ctxt option = {
      var role, st, b, psk, na, ca, skey, caf, mo; 
      
      mo <- None;
      if ((a, i) \in state_map) {
        (role, st) <- oget state_map.[a, i];
        match (st) with
        | IPending s m1 => {
          (b, psk, na, ca) <- s;
          if (dec_map.[(a, b), msg2_data a b ca, m2] is Some nb) {
            caf <$ dctxt;
            bad <- bad \/ exists pk ad, (pk, ad, caf) \in dec_map;
            if (!bad) {
              dec_map.[(a, b), msg3_data a b ca m2, caf] <- witness;
              mo <- Some caf;
              O.gen((msg3_data a b ca m2, caf));
              skey <@ O.f((msg3_data a b ca m2, caf), (a, b));
              state_map.[a, i] <- (Initiator, Accepted ((a, ca), m2, caf) (oget skey));
            }
          } else {
            state_map.[a, i] <- (Initiator, Aborted);
          }
        }
        | RPending _ _ _ => {}
        | Accepted _ _ => {}
        | Observed _ _ => {}
        | Aborted => {}
        end;
      }
      
      return mo;
    }

    proc send_fin(b : id, j : int, m3 : ctxt) : unit option = {
      var role, st, a, psk, na, nb, ca, cb, skey, mo;
      
      mo <- None;
      if ((b, j) \in state_map) {
        (role, st) <- oget state_map.[b, j];
        match (st) with
        | IPending _ _ => {}
        | RPending s m1 m2 => {
          (a, psk, na, nb, ca, cb) <- s;
          if(dec_map.[(a, b), msg3_data a b ca cb, m3] is Some nok) {
            skey <@ O.f((msg3_data a b ca cb, m3), (a, b));
            state_map.[b, j] <- (Responder, Accepted ((a, ca), cb, m3) (oget skey));
            mo <- Some tt;
          } else {
           state_map.[b, j] <- (Responder, Aborted);
          }
        }
        | Accepted _ _ => {}
        | Observed _ _ => {}
        | Aborted => {}
        end;
      }
      
      return mo;
    }

    proc rev_skey(a, i) = {
      var role, st, p_role, p_st, ps, p, k;
      var ko <- None;
  
      if ((a, i) \in state_map) {
        (role, st) <- oget state_map.[(a, i)];
        match st with
        | Accepted trace k' => {
          k <- k';
          ps <- get_partners (a, i) (Some trace) role state_map;
          if (card ps <= 1) {
            ps <- get_observed_partners (a, i) state_map;
            if (card ps <> 0) {
              p <- pick ps;
              (p_role, p_st) <- oget state_map.[p];
              if (p_st is Observed _ p_k) {
                k <- p_k;
              }
            }
            ko <- Some k;
            state_map.[(a, i)] <- (role, Observed trace k);
          }
        }
        | Observed _ k'  => ko <- Some k';
        | IPending _ _   => { }
        | RPending _ _ _ => { }
        | Aborted        => { }
        end;
      }
      return ko;
    }
  
    proc test = rev_skey
  }
  
  proc run() = {
    var b;
    WAKE_O.init_mem();
    b <@ D(WAKE_O).run();
    return b;
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* Ctxt Collision Reduction *)

op q_m1 : { int | 0 <= q_m1 } as ge0_q_m1.
op q_m2 : { int | 0 <= q_m2 } as ge0_q_m2.
op q_m3 : { int | 0 <= q_m3 } as ge0_q_m3.
clone Birthday as BD with
  type T <- ctxt,
  op uT <- dctxt,
  op q <- q_m1 + q_m2 + q_m3
  proof*.
realize ge0_q by smt(ge0_q_m1 ge0_q_m2 ge0_q_m3).

module Counter (W : GWAKE_out) : GWAKE_out_i = {
  var cm1, cm2, cm3 : int

  include W[send_fin, gen_pskey, test, rev_skey]

  proc init_mem() = {
    (cm1, cm2, cm3) <- (0, 0, 0);
  }
  
  proc send_msg1(x) = {
    var m;
    cm1 <- cm1 + 1;
    m <@ W.send_msg1(x);
    return m;
  }
  proc send_msg2(x) = {
    var m;
    cm2 <- cm2 + 1;
    m <@ W.send_msg2(x);
    return m;
  }
  proc send_msg3(x) = {
    var m;
    cm3 <- cm3 + 1;
    m <@ W.send_msg3(x);
    return m;
  }
}.

module Red_Coll_O_WAKE (S : BD.ASampler) = Game2 with {
  proc send_msg1 [
    ^if.^ca<$ ~ {ca <@ S.s();}
  ]

  proc send_msg2 [
    ^if.^match#Some.^cb<$ ~ {cb <@ S.s();}
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^caf<$ ~ { caf <@ S.s(); }
  ]
}.

module (Red_Coll (A : A_GWAKE) : BD.Adv) (S : BD.ASampler) = {
  proc a() = {
    var b;
    Red_Coll_O_WAKE(S).init_mem();
    Counter(Red_Coll_O_WAKE(S)).init_mem();
    b <@ A(Counter(Red_Coll_O_WAKE(S))).run();
  }
}.

(* ------------------------------------------------------------------------------------------ *)
(* ROM Reduction skeys *)

clone PROM.FullRO as KROc with
  type in_t    <= trace,
  type out_t   <= skey,
  op   dout  _ <= dskey,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

module (Red_ROM_sk_1 (D : A_GWAKE) : KROc.RO_Distinguisher) (O : KROc.RO) = {
  module WAKE_O : GWAKE_out = Game7 with {
    proc send_msg3 [
      ^if.^match#IPending.^match#Some.^if.^skey<$ ~ {
        O.sample(((a, ca), m2, caf));
        skey <- witness;
      }
    ]

    proc rev_skey [
      ^if.^match#Accepted.^if.^k<- ~ { k <@ O.get(trace); }
    ]
  }

  proc distinguish() = {
    var b;
    WAKE_O.init_mem();
    b <@ D(WAKE_O).run();
    return b;
  }
}.

module (Red_ROM_sk_2 (D : A_GWAKE) : KROc.RO_Distinguisher) (O : KROc.RO) = {
  module WAKE_O : GWAKE_out = Game7 with {
    proc send_msg3 [
      ^if.^match#IPending.^match#Some.^if.^skey<$ ~ {
        O.sample(((a, ca), m2, caf));
        skey <- witness;
      }
    ]

    proc rev_skey [
      ^if.^match#Accepted.^if.^k<- ~ { k <@ O.get(trace); }
    ]

    proc test [
      var v : skey
      ^if.^match#Accepted.^if.^k<- ~ {
        k <$ dskey;
        v <@ O.get(trace);
      }
    ]
  }

  proc distinguish() = {
    var b;
    WAKE_O.init_mem();
    b <@ D(WAKE_O).run();
    return b;
  }
}.
(* ------------------------------------------------------------------------------------------ *)
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GWAKE {-GWAKE0, -Game1, -Game2, -Game3, -Game4, -Game5, -Game6, -Game7, -Game8, -GAEAD0, -GAEAD1, -PRF0, -PRF1, -Red_AEAD, -Red_Coll, -Red_ROM, -Red_PRF, -Red_ROM_sk_1, -Red_ROM_sk_2, -RO, -FRO, -KROc.RO, -KROc.FRO, -BD.Sample}.

declare axiom A_ll:
forall (GW <: GWAKE_out{-A}),
  islossless GW.gen_pskey =>
  islossless GW.send_msg1 =>
  islossless GW.send_msg2 =>
  islossless GW.send_msg3 =>
  islossless GW.send_fin =>
  islossless GW.rev_skey => islossless GW.test => islossless A(GW).run.

declare axiom A_bounded_qs: forall (GW <: GWAKE_out{-A}), hoare[A(Counter(GW)).run: Counter.cm1 = 0 /\ Counter.cm2 = 0 /\ Counter.cm3 = 0 ==> Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2 /\ Counter.cm3 <= q_m3].

equiv test:Game5.gen_pskey ~ Game6.gen_pskey: 
={arg} /\ ={state_map, dec_map, prfkey_map, psk_map}(Game5, Game6)
==>
={state_map, dec_map, prfkey_map, psk_map}(Game5, Game6).
proof. by sim />. qed.

equiv test1:Game5.send_msg1 ~ Game6.send_msg1:
={arg} /\ ={state_map, dec_map, prfkey_map, psk_map, bad}(Game5, Game6)
==>
={state_map, dec_map, prfkey_map, psk_map, bad}(Game5, Game6).
proof. sim />. qed.

equiv test2:Game6.send_msg1 ~ Game5.send_msg1:
={arg} /\ ={state_map, dec_map, prfkey_map, psk_map, bad}(Game6, Game5)
==>
={state_map, dec_map, prfkey_map, psk_map, bad}(Game6, Game5).
proof. sim />. qed.

hoare Game6_inv_send_msg1: Game6.send_msg1:
  (Game5_inv_full Game6.state_map Game6.dec_map Game6.prfkey_map)
  ==>
  (Game5_inv_full Game6.state_map Game6.dec_map Game6.prfkey_map).
proof.
by conseq test2 Game5_inv_send_msg1 => /#.
qed.

inductive Red_inv (sm: (id * int, role * instance_state) fmap) (dm : ((id * id) * msg_data * ctxt, nonce) fmap) (pkm : (trace, skey) fmap) (a: id) (i: int) =
| Red_undef of
    (sm.[a, i] = None)
| Red_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| Red_ipending b ca of
    (sm.[a, i] = Some (Initiator, IPending (b, witness, witness, ca) (a, ca)))
    & (forall m2 m3, ((a, ca), m2, m3) \notin pkm)
    & (((a, b), msg1_data a b, ca) \in dm) 
    & (forall m2 m3, ((a, b), msg3_data a b ca m2, m3) \notin dm)
| Red_rpending b cb ca of
    (sm.[a, i] = Some (Responder, RPending (b, witness, witness, witness, cb, ca) (b, cb) ca))
    & (forall m3, ((b, cb), ca, m3) \notin pkm)
    & (((b, a), msg2_data b a cb, ca) \in dm) 
| Red_iaccepted b m1 m2 m3 k of
    (sm.[a, i] = Some (Initiator, Accepted ((a, m1), m2, m3) k))
    & (((a, m1), m2, m3) \notin pkm)
    & (((a, b), msg3_data a b m1 m2, m3) \in dm) 
| Red_raccepted b m1 m2 m3 k of
    (sm.[a, i] = Some (Responder, Accepted ((b, m1), m2, m3) k))
    & (((b, m1), m2, m3) \notin pkm)
    & (((b, a), msg3_data b a m1 m2, m3) \in dm) 
| Red_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma Red_inv_neq a i c j v sm dm km:
! (c = a /\ j = i) =>
Red_inv sm dm km c j =>
Red_inv sm.[(a, i) <- v] dm km c j.
proof.
move=> neq
[
smbj
| r smbj
| s m1 smbj
| s m1 m2 smbj
| b m1 m2 m3 k smbj
| b m1 m2 m3 k smbj
| r tr k smbj
].
+ apply Red_undef.
  by rewrite get_set_neqE.
+ apply (Red_aborted _ _ _ _ _ r).
  by rewrite get_set_neqE.
+ apply (Red_ipending _ _ _ _ _ s m1) => //.
  by rewrite get_set_neqE.
+ apply (Red_rpending _ _ _ _ _ s m1 m2)=> //.
  by rewrite get_set_neqE.
+ apply (Red_iaccepted _ _ _ _ _ b m1 m2 m3 k)=> //.
  by rewrite get_set_neqE.
+ apply (Red_raccepted _ _ _ _ _ b m1 m2 m3 k)=> //.
  by rewrite get_set_neqE.
apply (Red_observed _ _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

lemma Red_inv_neq_dm a i m sm (dm : (_, _) fmap) km:
(forall a b ca cb, ((a, b), msg2_data a b ca, cb) \in dm => ((a, b), msg1_data a b, ca) \in dm) =>
(forall a b ca cb caf, ((a, b), msg3_data a b ca cb, caf) \in dm => ((a, b), msg2_data a b ca, cb) \in dm) =>
! (exists pk ad, (pk, ad, m) \in dm) =>
Red_inv sm dm km a i =>
forall pk ad, Red_inv sm dm.[(pk, ad, m) <- witness] km a i.
proof.
move=> dm1 dm2 uniq
[ 
smbj
| r smbj
| b ca smbj nin dmin dmnin
| b ca cb smbj nin dmin
| b m1 m2 m3 k smbj nin dmin
| b m1 m2 m3 k smbj nin dmin
| r tr k smbj
] pk ad.
+ exact Red_undef.
+ exact (Red_aborted _ _ _ _ _ r).
+ apply (Red_ipending _ _ _ _ _ b ca)=> //.
  by rewrite mem_set dmin.
  smt(get_setE mem_set). 
  move=> m2; rewrite mem_set (dmnin1 m2).
+ apply (Red_rpending _ _ _ _ _ b ca cb)=> //.
  by rewrite mem_set dmin.  
+ apply (Red_iaccepted _ _ _ _ _ b m1 m2 m3 k)=> //.
  by rewrite mem_set dmin.  
+ apply (Red_raccepted _ _ _ _ _ b m1 m2 m3 k)=> //.
  by rewrite mem_set dmin.  
exact (Red_observed _ _ _ _ _ r tr k).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 7: Move randomly sample the skey in test *)
lemma Step7 &m:
    Pr[E_GWAKE(Game7, A).run() @ &m : res] = Pr[E_GWAKE(Game8, A).run() @ &m : res].
proof.
byequiv => //.
proc*.
outline {1} [1] { r <@ KROc.MainD(Red_ROM_sk_1(A), KROc.RO).distinguish(); }.
+ inline*; wp.
  call(: ={state_map, psk_map, dec_map, bad, prfkey_map}(Game7, Red_ROM_sk_1.WAKE_O)
         /\ Game7.sk_map{1} = KROc.RO.m{2}
  /\ (forall h r tr k, Game7.state_map.[h] = Some (r, Accepted tr k) => tr \in Game7.sk_map){1}
  /\ (forall a b m1 m2 m3, ((a, b), msg3_data a b m1 m2, m3) \in Game7.dec_map => ((a, m1), m2, m3) \in Game7.sk_map){1}
  /\ (forall m1 m2 m3, (forall pk ad, (pk, ad, m3) \notin Game7.dec_map) => (m1, m2, m3) \notin Game7.sk_map){1}
  ).
  
  - by sim />.  

  - proc; inline*. 
    sp; if => //.
    auto => />.
    smt(mem_set get_setE).
  
  - proc; inline*.
    sp; if => //.
    match = => //.
    + auto => />. 
      smt(get_setE).
    auto => />.
    smt(mem_set get_setE).
  
  - proc; inline*.
    sp; if=> //. 
    sp; match = => //.
    + smt().  
    move=> s m1.
    sp; match =.
    + smt().
    + auto=> />.
      smt(get_setE).
    move=> nb.
    seq 1 1 : (#pre /\ ={caf}); 1: by auto.
    sp; if=> //.
    auto=> />.
    smt(mem_set get_setE).
  
  - proc; inline*.
    sp; if=> //. 
    sp; match = => //.
    + smt().
    move=> s m1 m2. 
    sp; match =.
    + smt().
    + auto=> />.
      smt(get_setE).
    move=> nok.
    auto=> />.
    smt(get_setE).

  - proc; inline*. 
    sp; if => //.
    sp; match = => //; last by auto.
    + smt().
    move=> tr k'.
    sp; if => //.
    + smt().
    rcondf{2} ^if; 1: by auto=> /#.
    kill {2} ^r<$; 1: by islossless.
    wp ^if ^if.
    conseq (: _ ==> ={k}).
    + move=> /> &1 &2.
      smt(get_setE).
    move=> />.
    sp; if => //.
    sp; match =; auto=> />.
    smt().
   
  - proc; inline*. 
    sp; if => //.
    sp; match = => //; last by auto.
    + smt().
    move=> tr k'.
    sp; if => //.
    + smt().
    rcondf{2} ^if; 1: by auto=> /#.
    kill {2} ^r<$; 1: by islossless.
    wp ^if ^if.
    conseq (: _ ==> ={k}).
    + move=> /> &1 &2.
      smt(get_setE).
    move=> />.
    sp; if => //.
    sp; match =; auto=> />.
    smt().
  
  auto=> />.
  smt(emptyE).

have ll : forall (t : trace), is_lossless dskey by move=> _; exact dskey_ll.
rewrite equiv [{1} 1 (KROc.FullEager.RO_LRO (Red_ROM_sk_1(A)) ll)].
outline {2} [1] { r <@ KROc.MainD(Red_ROM_sk_2(A), KROc.RO).distinguish(); }.
+ rewrite equiv [{2} 1 (KROc.FullEager.RO_LRO (Red_ROM_sk_2(A)) ll)].
  inline*; wp.
  call(: 
      ={state_map, psk_map, dec_map, bad, prfkey_map, sk_map}(Red_ROM_sk_1.WAKE_O, Red_ROM_sk_2.WAKE_O)
      /\ (forall t, t \in KROc.RO.m{1} <=> t \in KROc.RO.m{2})
      /\ (forall a m1 m2 m3, (forall pk ad, (pk, ad, m1) \notin Red_ROM_sk_1.WAKE_O.dec_map) => ((a, m1), m2, m3) \notin KROc.RO.m){1}
      /\ (forall m1 m2 m3, (forall pk ad, (pk, ad, m2) \notin Red_ROM_sk_1.WAKE_O.dec_map) => (m1, m2, m3) \notin KROc.RO.m){1}
      /\ (forall m1 m2 m3, (forall pk ad, (pk, ad, m3) \notin Red_ROM_sk_1.WAKE_O.dec_map) => (m1, m2, m3) \notin KROc.RO.m){1}
      /\ (forall a b ca cb, ((a, b), msg2_data a b ca, cb) \in Red_ROM_sk_1.WAKE_O.dec_map => ((a, b), msg1_data a b, ca) \in Red_ROM_sk_1.WAKE_O.dec_map){1}
      /\ (forall a b ca cb caf, ((a, b), msg3_data a b ca cb, caf) \in Red_ROM_sk_1.WAKE_O.dec_map => ((a, b), msg2_data a b ca, cb) \in Red_ROM_sk_1.WAKE_O.dec_map){1}
      /\ (forall a i, Red_inv Red_ROM_sk_1.WAKE_O.state_map Red_ROM_sk_1.WAKE_O.dec_map KROc.RO.m a i){1}
  ).
  
  - by sim />.  

  - proc; inline*. 
    sp; if => //.
    seq 1 1 : (#pre /\ ={ca}); 1: by auto.
    sp 1 1; if => //.
    auto => />.
    smt(mem_set get_setE Red_ipending Red_inv_neq Red_inv_neq_dm).
  
  - proc; inline*.
    sp; if => //.
    match = => //.
    + auto => />. 
      smt(get_setE Red_aborted Red_inv_neq Red_inv_neq_dm).
    auto => />.
    smt(get_setE Red_rpending Red_inv_neq Red_inv_neq_dm).
  
  - proc; inline*.
    sp; if=> //. 
    sp; match = => //.
    + smt().  
    move=> s m1.
    sp; match =.
    + smt().
    + auto=> />.
      smt(get_setE Red_aborted Red_inv_neq Red_inv_neq_dm).
    move=> nb.
    seq 1 1 : (#pre /\ ={caf}); 1: by auto.
    sp; if=> //.
    auto=> />.
    smt(get_setE mem_set Red_iaccepted Red_inv_neq Red_inv_neq_dm).
  
  - proc; inline*.
    sp; if=> //. 
    sp; match = => //.
    + smt().
    move=> s m1 m2. 
    sp; match =.
    + smt().
    + auto=> />.
      smt(get_setE Red_aborted Red_inv_neq).
    move=> nok.
    auto=> />.
    move=> &1 &2 dm _ sm1 sm2 inv1 inv2 inv3 inv4 inv5 inv6 inv7 bjin.
    move=> a' i'.
    case ((a', i') = (b, j){2}) => /> => [|neq_ai].
    + apply (Red_raccepted _ _ _ _ _ a{2} ca{2} cb{2} m3{2} witness).
      + by rewrite get_set_sameE.
      + by case: (inv7 b{2} j{2})=> /#.
      smt().
    smt(Red_inv_neq).

  - proc; inline*. 
    sp; if => //.
    sp; match = => //; last by auto.
    + smt().
    move=> tr' k'.
    sp; if => //.
    + smt().
    sp; seq 1 1 : (={r} /\ #pre); 1: by auto.
    rcondt {1} ^if.
    + auto=> />.
      move=> &1 sm _ _ _ _ _ _ _ inv aiin.
      by case: (inv a{m0} i{m0})=> /#.
    rcondt {2} ^if.
    + auto=> />.
      move=> &1 sm _ eq_in  _ _ _ _ _ inv aiin.
      by case: (inv a{m0} i{m0})=> /#.
    wp ^if ^if.
    sp 1 1.
    conseq (: _ ==> ={k}).
    + move=> /> &1 &2.
      move=> mr ml smr sml inv1 inv2 inv3 inv4 inv5 inv6 inv7 /some_oget sm card sk.
      rewrite -sml in sm.
      case: (inv7 a{2} i{2}); rewrite sm //=.
      + move=> /> b m1' m2' m3' role xeq ainin aidmin.
      do! split; 1..5: smt(get_setE).
      move=> a' i'.
      case ((a', i') = (a, i){2}) => /> => [|neq_ai].
      + apply (Red_observed _ _ _ _ _ Initiator ((a{2}, m1'), m2', m3') sk).
        by rewrite get_set_sameE.
      apply Red_inv_neq=> //.
      case: (inv7 a' i')=>
    [
    smbj
    | r smbj
    | s m1 smbj nin dmin
    | s m1 m2 smbj nin dmin
    | r tr k smbj nin dmin
    | r tr k smbj nin dmin
    | r tr k smbj
    ].
    + exact Red_undef.
    + exact (Red_aborted _ _ _ _ _ r).
    + apply (Red_ipending _ _ _ _ _ s m1) => //.
      move=> m2 m3; rewrite mem_set (nin m2 m3) /=.
      case (m1 = m1') => />.
      smt(get_setE mem_set).
    + apply (Red_rpending _ _ _ _ s m1 m2)=> //.
    by rewrite get_set_neqE.
    + apply (Red_accepted _ _ _ _ r tr k)=> //.
    by rewrite get_set_neqE.
    apply (Red_observed _ _ _ _ r tr k)=> //.
    by rewrite get_set_neqE.
      smt(get_setE Red_inv_neq Red_observed).
    move=> />.
    sp; if => //.
    sp; match =; auto=> />.
    smt().
   
  - proc; inline*. 
    sp; if => //.
    sp; match = => //; last by auto.
    + smt().
    move=> tr k'.
    rcondf{2} ^if; 1: by auto=> /#.
    kill {2} ^r<$; 1: by islossless.
    sp; if => //.
    + smt().
    wp 2 2.
    conseq (: _ ==> ={k}).
    + move=> /> &1 &2.
      smt(get_setE).
    move=> />.
    sp; if => //.
    sp; match =; auto=> />.
    smt().
  
  auto=> />.
  smt(emptyE).

inline*; wp.
call(: ={state_map, psk_map, dec_map, bad, prfkey_map}(Red_ROM_sk_2.WAKE_O, Game8)
       /\ (Game8.sk_map{2} = KROc.RO.m{1})
/\ (forall h r tr k, Game8.state_map{2}.[h] = Some (r, Accepted tr k) => tr \in Game8.sk_map{2})
/\ (forall a b m1 m2 m3, ((a, b), msg3_data a b m1 m2, m3) \in Game8.dec_map => ((a, m1), m2, m3) \in Game8.sk_map){2}
/\ (forall m1 m2 m3, (forall pk ad, (pk, ad, m3) \notin Game8.dec_map) => (m1, m2, m3) \notin Game8.sk_map){2}
).

- by sim />.  

- proc; inline*. 
  sp; if => //.
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if => //.
  match = => //.
  + auto => />. 
    smt(get_setE).
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if=> //. 
  sp; match = => //.
  + smt().  
  move=> s m1.
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move=> nb.
  seq 1 1 : (#pre /\ ={caf}); 1: by auto.
  sp; if=> //.
  auto=> />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if=> //. 
  sp; match = => //.
  + smt().
  move=> s m1 m2. 
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move=> nok.
  auto=> />.
  smt(get_setE).

- proc; inline*. 
  sp; if => //.
  sp; match = => //; last by auto.
  + smt().
  move=> tr k'.
  rcondf{1} ^if; 1: by auto=> /#.
  kill {1} ^r<$; 1: by islossless.
  sp 1 0; seq 1 1 : (={k} /\ #pre).
  + auto=> />.
  auto=> />.
  smt(get_setE).
 
- proc; inline*. 
  sp; if => //.
  sp; match = => //; last by auto.
  + smt().
  move=> tr k'.
  seq 1 1 : (k{1} = k{2} /\ #pre); 1: by auto.
  rcondf{1} ^if; 1: by auto=> /#.
  kill {1} ^r<$; 1: by islossless.
  sp; if => //.
  + smt().
  auto=> />.
  smt(get_setE).
auto=> />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 6: Remove skeys from the state using sk_map to retrieve. *)

local op clear_sk (s : instance_state) =
match s with
| IPending _ _ => s
| RPending _ _ _ => s
| Accepted tr k => Accepted tr witness
| Observed _ _ => s
| Aborted => s
end.

local lemma eq_partners_sk h tr r sml smr: 
  (forall h, omap (fun (v: role * instance_state) => let (r, s) = v in (r, clear_sk s)) sml.[h] = smr.[h]) =>
get_partners h tr r sml = get_partners h tr r smr.
proof.
move=> eqsm.
rewrite /get_partners fsetP => h'.
rewrite !mem_fdom !mem_filter /=.
by smt().
qed.

local lemma eq_obs_partners_sk h sml smr: 
  (forall h, omap (fun (v: role * instance_state) => let (r, s) = v in (r, clear_sk s)) sml.[h] = smr.[h]) =>
get_observed_partners h sml = get_observed_partners h smr.
proof.
move=> eqsm.
rewrite /get_observed_partners.
congr.
+ rewrite fun_ext => bj.
  rewrite -(eqsm bj) //=.
  case: (sml.[bj])=> //.
  by move=> [r' []] // [].
rewrite -(eq_partners_sk _ _ _ sml smr eqsm). 
rewrite -(eqsm h) /s /r //=.
case: (sml.[h])=> //.
by move=> [r' []] // [].
qed.

lemma Step6 &m:
    Pr[E_GWAKE(Game6, A).run() @ &m : res] = Pr[E_GWAKE(Game7, A).run() @ &m : res].
proof.
byequiv => //.
proc; inline*.
call (:
    ={psk_map, dec_map, bad, prfkey_map, sk_map}(Game6, Game7)
/\ (forall h, omap (fun v => let (r, s) = v in (r, clear_sk s)) Game6.state_map.[h]{1} = Game7.state_map.[h]{2})
/\ (forall h r tr k, Game6.state_map.[h] = Some (r, Accepted tr k) => Game6.sk_map.[tr] = Some k){1}
/\ (forall a b m1 m2 m3, ((a, b), msg3_data a b m1 m2, m3) \in Game6.dec_map => ((a, m1), m2, m3) \in Game6.sk_map){1}
/\ (forall m, (forall pk ad , (pk, ad, m) \notin Game6.dec_map) => (forall a m1 m2 m3, ((a, m1), m2, m3) \in Game6.sk_map => m3 <> m)){1}
).

- by sim />.

- proc; inline*. 
  sp; if => //.
  + smt().
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if => //.
  + smt().
  match = => //.
  + auto => />. 
    smt(get_setE).
  auto => />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if=> //. 
  + smt().
  sp; match; 1..5: smt(); 2..5: by auto.
  move=> sl m1l sr m1r.
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move=> nb.
  seq 1 1 : (#pre /\ ={caf}); 1: by auto.
  sp; if=> //.
  auto=> />.
  smt(mem_set get_setE).

- proc; inline*.
  sp; if=> //. 
  + smt().
  sp; match; 1..5: smt(); 1,3..5: by auto.
  move=> sl m1l m2l sr m1r m2r.
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move=> nok.
  auto=> />.
  smt(get_setE).

- proc; inline. 
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,2,5: by auto.
  + move=> tr k tr' k'.
    sp 1 1.
    seq 0 0 : (={k} /\ #pre).
    + auto=> />; smt().
    sp ^if & -1 ^if & -1; if=> //.
    + smt(eq_partners_sk).
    sp ^if & -1 ^if & -1; if.
    + move=> /> &1 &2 smr sml eqsm.
      by rewrite (eq_obs_partners_sk (a, i){2} Game6.state_map{1} Game7.state_map{2}).
    + seq 1 1 : (={ps, p} /\ #pre).
      + auto=> /> &1 &2 smr sml eqsm.
        by rewrite (eq_obs_partners_sk (a, i){2} Game6.state_map{1} Game7.state_map{2}).
      wp 2 2.
      conseq (: _ ==> ={k}).
      + move=> /> &1 &2 _ + + eqsm invl a_in _ _.
        rewrite -(eqsm (a, i){2}).
        by case: (Game6.state_map{1}.[(a, i){2}]); smt(get_setE).
      auto=> /> &1 &2 + + + eqsm invl a_in _ _.
      rewrite -(eqsm (a, i){2}) -(eqsm p{2}).
      by case: (Game6.state_map{1}.[p{2}])=> /#.
    auto=> /> &1 &2 + + eqsm invl a_in _ _.
    rewrite -(eqsm (a, i){2}).
    by case: (Game6.state_map{1}.[(a, i){2}]); smt(get_setE).
  by auto; smt().

- proc; inline. 
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,2,5: by auto.
  + move=> tr k tr' k'.
    sp 1 1.
    seq 0 0 : (={k} /\ #pre).
    + auto=> />; smt().
    sp ^if & -1 ^if & -1; if=> //.
    + smt(eq_partners_sk).
    sp ^if & -1 ^if & -1; if.
    + move=> /> &1 &2 smr sml eqsm.
      by rewrite (eq_obs_partners_sk (a, i){2} Game6.state_map{1} Game7.state_map{2}).
    + seq 1 1 : (={ps, p} /\ #pre).
      + auto=> /> &1 &2 smr sml eqsm.
        by rewrite (eq_obs_partners_sk (a, i){2} Game6.state_map{1} Game7.state_map{2}).
      wp 2 2.
      conseq (: _ ==> ={k}).
      + move=> /> &1 &2 _ + + eqsm invl a_in _ _.
        rewrite -(eqsm (a, i){2}).
        by case: (Game6.state_map{1}.[(a, i){2}]); smt(get_setE).
      auto=> /> &1 &2 + + + eqsm invl a_in _ _.
      rewrite -(eqsm (a, i){2}) -(eqsm p{2}).
      by case: (Game6.state_map{1}.[p{2}])=> /#.
    auto=> /> &1 &2 + + eqsm invl a_in _ _.
    rewrite -(eqsm (a, i){2}).
    by case: (Game6.state_map{1}.[(a, i){2}]); smt(get_setE).
  by auto; smt().

auto=> />.
by smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 0: Inline procedure calls, and remove pskeys from the state using psk_map to retrieve. *)

local op clear_psk (s : instance_state) =
match s with
| IPending st m1 => 
 /=  let (id, psk, na, ca) = st in IPending (id, witness, na, ca) m1 
| RPending st m1 m2 => 
  let (id, psk, na, nb, ca, cb) = st in RPending (id, witness, na, nb, ca, cb) m1 m2 
| Accepted _ _ => s
| Observed _ _ => s
| Aborted => s
end.

local lemma eq_partners h tr r sml smr: 
  (forall h, omap (fun (v: role * instance_state) => let (r, s) = v in (r, clear_psk s)) sml.[h] = smr.[h]) =>
get_partners h tr r sml = get_partners h tr r smr.
proof.
move=> eqsm.
rewrite /get_partners.
congr.
apply fmap_eqP => h'.
rewrite !filterE -(eqsm h') /=. 
case: (sml.[h'])=> //=.
by move=> [r' []] // [] /= /#.
qed.

local lemma eq_obs_partners h sml smr: 
  (forall h, omap (fun (v: role * instance_state) => let (r, s) = v in (r, clear_psk s)) sml.[h] = smr.[h]) =>
get_observed_partners h sml = get_observed_partners h smr.
proof.
move=> eqsm.
rewrite /get_observed_partners.
congr.
+ rewrite fun_ext => bj.
  rewrite -(eqsm bj) //=.
  case: (sml.[bj])=> //.
  by move=> [r' []] // [].
rewrite -(eq_partners _ _ _ sml smr eqsm). 
rewrite -(eqsm h) /s /r //=.
case: (sml.[h])=> //.
by move=> [r' []] // [].
qed.

lemma Step0 &m:
    Pr[E_GWAKE(GWAKE0(NSL), A).run() @ &m : res] = Pr[E_GWAKE(Game1, A).run() @ &m : res].
proof.
byequiv => //.
proc; inline*.
call (:
    ={psk_map}(GWAKEb, Game1)
/\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
/\ (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i){1}
).
- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
  ) GWAKE0_inv_gen_pskey _ => //.
  proc.
  by if; auto.

- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
  ) GWAKE0_inv_send_msg1 _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  auto=> />.
  smt(get_setE).

- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
  ) GWAKE0_inv_send_msg2 _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  sp; match =.
  + smt().
  + auto=> />.
    smt(get_setE).
  move=> na.
  by match Some {1} ^match; auto; smt(get_setE).

- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
  ) GWAKE0_inv_send_msg3 _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 2..5: by auto.
  move=> sil m1l sir m1r.
  sp; match =.
  + auto=> />.
    move=> &1 &2 smr sml inv_sm invl sms.
    case: (invl a{2} i{2})=> /#.
  + match None {1} ^match; auto; smt(get_setE).
  move=> nb.
  match Some {1} ^match.
  + auto; smt(get_setE).
  auto=> />.
  move=> &1 &2 + + + sml + invl.
  case: (invl a{2} i{2}); 1,2,4,5,6: smt().
  smt(get_setE).

- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
  ) GWAKE0_inv_send_fin _ => //.
  proc; inline.
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,3,4,5: by auto.
  move=> sil m1l m2l sir m1r m2r.
  sp; match =.
  + auto=> />. 
    move=> &1 &2 smr sml inv_sm invl bj_in.
    case: (invl b{2} j{2})=> /#.
  + match None {1} ^match; auto; smt(get_setE).
  move=> nb.
  match Some {1} ^match.
  + auto; smt(get_setE).
  auto=> />.
  move=> &1 &2 + + + sml + invl.
  case: (invl b{2} j{2}); 1,2,3,5,6: smt().
  smt(get_setE).

- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
  ) GWAKE0_inv_rev_skey _ => //.
  proc; inline. 
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,2,5: by auto.
  + move=> tr k tr' k'.
    sp ^if & -1 ^if & -1; if=> //.
    + smt(eq_partners).
    wp 2 2.
    conseq (: _ ==> ={k}).
    + move=> /> &1 &2 + + eqsm invl a_in _.
      rewrite -(eqsm (a, i){2}).
      by case: (GWAKEb.state_map{1}.[(a, i){2}]); smt(get_setE).
    sp ^if & -1 ^if & -1.
    seq 0 0 : (={ps} /\ #pre).
    + auto=> /> &1 &2 smr sml eqsm.
      by rewrite (eq_obs_partners (a, i){2} GWAKEb.state_map{1} Game1.state_map{2}).
    if=> //; first last.
    + auto=> /> &1 &2 _ + + eqsm invl a_in.
      rewrite -(eqsm (a, i){2}).
      by case: (GWAKEb.state_map{1}.[(a, i){2}]); smt(get_setE).
    auto=> /> &1 &2 -> + + eqsm invl a_in.
    pose p:=(pick (get_observed_partners (a{2}, i{2}) GWAKEb.state_map{1})).
    rewrite -(eqsm (a, i){2}) -(eqsm p).
    case: (GWAKEb.state_map{1}.[(a, i){2}])=> />.
    + by case: (GWAKEb.state_map{1}.[p])=> /#.
    by case: (GWAKEb.state_map{1}.[p])=> /#.
  by auto; smt().

- conseq (: ={res}
          /\ ={psk_map}(GWAKEb, Game1)
          /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_psk s)) GWAKEb.state_map.[h]{1} = Game1.state_map.[h]{2})
     ) GWAKE0_inv_test _ => //.
  proc; inline. 
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,2,5: by auto.
  + move=> tr k tr' k'.
    sp ^if & -1 ^if & -1; if=> //.
    + smt(eq_partners).
    sp ^if & -1 ^if & -1; if.
    + move=> /> &1 &2 smr sml eqsm.
      by rewrite (eq_obs_partners (a, i){2} GWAKEb.state_map{1} Game1.state_map{2}).
    + seq 1 1 : (={ps, p} /\ #pre).
      + auto=> /> &1 &2 smr sml eqsm.
        by rewrite (eq_obs_partners (a, i){2} GWAKEb.state_map{1} Game1.state_map{2}).
      wp 2 2.
      conseq (: _ ==> ={k, role} /\ tr = tr').
      + move=> /> &1 &2 _ + + eqsm invl a_in _ _.
        rewrite -(eqsm (a, i){2}).
        by case: (GWAKEb.state_map{1}.[(a, i){2}]); smt(get_setE).
      auto=> /> &1 &2 + + + eqsm invl a_in _ _.
      rewrite -(eqsm (a, i){2}) -(eqsm p{2}).
      case: (GWAKEb.state_map{1}.[(a, i){2}])=> />.
      + by case: (GWAKEb.state_map{1}.[p{2}])=> /#.
      by case: (GWAKEb.state_map{1}.[p{2}])=> /#.
    auto=> /> &1 &2 + + eqsm invl a_in _ _.
    rewrite -(eqsm (a, i){2}).
    by case: (GWAKEb.state_map{1}.[(a, i){2}]); smt(get_setE).
  by auto; smt().

auto=> />.
split; 1: smt(emptyE).
move=> a i. 
apply GWAKE0_undef.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 1: Apply the AEAD assumption. *)

lemma Step1 &m:
    `|Pr[E_GWAKE(Game1, A).run() @ &m : res] - Pr[E_GWAKE(Game2, A).run() @ &m : res]|
  = 
    `|Pr[E_GAEAD(GAEAD0, Red_AEAD(A)).run() @ &m : res] - Pr[E_GAEAD(GAEAD1, Red_AEAD(A)).run() @ &m : res]|.
proof.
do! congr.
+ byequiv => //.
  proc; inline*.
  wp.
  call (:
        ={psk_map}(Game1, GAEADb)
     /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
     /\ (forall a i, Game1_inv Game1.state_map Game1.psk_map a i){1}
  )=> //.

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_gen_pskey _ => //.
    by proc; if; auto.

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_send_msg1 _ => //.
    proc; inline.
    sp; if=> //.
    by match Some {2} ^match; auto; smt().

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_send_msg2 _ => //.
    proc; inline.
    sp; if=> //.
    match Some {2} ^match.
    + auto; smt().
    sp; match =.
    + smt().
    + by auto. 
    move=> na.
    by match Some {2} ^match; auto; smt().

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_send_msg3 _ => //.
    proc; inline.
    sp; if=> //.
    sp; match = => //. 
    + smt().
    move=> st m1.
    exlim Game1.state_map{1}, Game1.psk_map{1}, a{1}, i{1} => sm pm a i.
    case @[ambient] _: (forall a i, Game1_inv sm pm a i) => [inv|?]; 2: by exfalso => /#. 
    case @[ambient] _: (inv a i); 1,2,4,5,6: (move=> *; exfalso=> /#).
    move=> b na c1 kab smai pmab.
    match Some {2} ^match; 1: by auto=> /#.
    sp; match =.
    + by auto=> /#. 
    + by auto=> /#.
    move=> nb.
    match Some {2} ^match; 1: by auto=> /#.
    by auto=> /#.

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_send_fin _ => //.
    proc; inline.
    sp; if=> //.
    sp; match = => //.
    + move=> /#.
    move=> st m1 m2.
    match Some {2} ^match.
    + auto=> />. 
      move=> &hr smr sml invl bj_in.
      by case: (invl b{m0} j{m0})=> /#.
    by sp; match =; auto=> /#.

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_rev_skey _ => //.
    by sim. 

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_test _ => //.
    by sim. 
  
  auto=> />.
  move=> a i.
  exact /Game1_undef/emptyE.

byequiv => //.
proc; inline*.
wp.
call (:
      ={psk_map}(Game2, GAEADb)
      /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
      /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
      /\ (forall a i, Game1_inv Game2.state_map Game2.psk_map a i){1}
).
- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_gen_pskey _ => //.
  proc.
  by if; auto.

- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_send_msg1 _ => //.
  proc; inline.
  sp; if=> //.
  rcondt{2} ^if; 1: by auto.
  swap {2} ^c<$ @ ^na<$.
  by auto.

- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_send_msg2 _ => //.
  proc; inline.
  sp; if=> //.
  rcondt {2} 5; 1: by auto.
  sp; match = => //.
  + by auto.
  move=> na.
  rcondt {2} ^if; 1: by auto.
  swap {2} ^c0<$ @ ^nb<$.
  by auto.

- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_send_msg3 _ => //.
  proc; inline.
  sp; if=> //.
  sp; match = => //.
  + smt().
  move=> st m1.
  rcondt {2} ^if.
  + auto=> />.
    move=> &hr smr sml invl ai_in.
    by case: (invl a{m0} i{m0})=> /#.
  sp; match =.
  + by auto.
  + by auto.
  move=> nb.
  rcondt {2} ^if.
  + auto=> />.
    move=> &hr decl decr smr sml invl ai_in ok _.
    by case: (invl a{m0} i{m0})=> /#.
  swap {2} ^c0<$ @ ^ok<$.
  by auto.

- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_send_fin _ => //.
  proc; inline.
  sp; if=> //.
  sp; match = => //.
  + smt().
  move=> st m1 m2.
  rcondt {2} 6.
  + auto=> />.
    move=> &hr smr sml invl ai_in.
    by case: (invl b{m0} j{m0})=> /#.
  by sp; match =; auto.

- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_rev_skey _ => //.
  by sim.

- conseq (: ={res}
       /\ ={psk_map}(Game2, GAEADb)
       /\ ={state_map}(Game2, Red_AEAD.WAKE_O)
       /\ Game2.dec_map{1} = GAEAD1.ctxts{2}
  ) Game2_inv_test _ => //.
  by sim.

auto=> /> a i.
exact /Game1_undef/emptyE.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 2a: Remove collisions of all produced ciphertexts. *)

lemma Step2 &m: `| Pr[E_GWAKE(Game2, A).run() @ &m : res] - Pr[E_GWAKE(Game3, A).run() @ &m : res] | <= Pr[E_GWAKE(Game2, A).run() @ &m : Game2.bad].
proof.
rewrite StdOrder.RealOrder.distrC.
byequiv (: _ ==> _) : Game3.bad => //; first last.
+ move=> &1 &2.
  by case: (Game2.bad{2}).
symmetry; proc; inline*.
call (: Game3.bad, ={bad, psk_map, state_map, dec_map}(Game2, Game3), ={bad}(Game2, Game3)) => //.
+ exact A_ll.

+ by proc; inline*; auto; if; auto.
+ move=> &2 ->.
  proc; sp; if; auto=> />.
  by rewrite dpskey_ll.  
+ move=> &1.
  proc; sp; if; auto.
  by rewrite dpskey_ll. 
 
+ proc.
  sp; if=> //.
  seq 1 1: (#pre /\ ={ca}); 1: by auto.
  sp 1 1.
  by if{2}; auto=> />.
+ move=> &2 ->.
  proc; sp; if=> //; auto.
  by rewrite dnonce_ll dctxt_ll.
+ move=> &1.
  proc; sp; if=> //.
  rcondf ^if; auto=> />.
  by rewrite dctxt_ll.

+ proc.
  sp; if=> //.
  match = => //.
  + by auto.
  move=> na.
  seq 1 1: (#pre /\ ={cb}); 1: by auto.
  sp 0 1.
  by if{2}; auto=> />.
+ move=> &2 ->.
  proc; sp; if=> //; match =; auto.
  by rewrite dnonce_ll dctxt_ll.
+ move=> &1.
  proc; sp; if=> //; match =; auto.
  rcondf ^if; auto=> />.
  by rewrite dctxt_ll.

+ proc.
  sp; if=> //.
  sp; match = => //.
  - smt().
  move => s m1.
  sp; match = => //.
  + by auto.  
  move=> nb.
  seq 1 1: (#pre /\ ={caf}); 1: by auto.
  sp 0 1.
  by if{2}; auto=> />.
+ move=> &2 ->.
  proc; sp; if=> //; sp; match =; auto; sp; match =; auto.
  by rewrite dnonce_ll dctxt_ll.
+ move=> &1.
  proc; sp; if=> //; sp; match =; auto; sp; match =; auto.
  rcondf ^if; auto=> />.
  by rewrite dctxt_ll.

+ proc.
  sp; if=> //.
  sp; match =; auto; smt(). 
+ move=> &2 ->.
  proc; sp; if=> //; sp; match =; auto; smt().
+ move=> &1.
  proc; sp; if=> //; sp; match =; auto; smt().

+ proc.
  sp; if=> //.
  sp; match =; auto; smt(). 
+ move=> &2 ->.
  proc; sp; if=> //; sp; match =; auto; smt().
+ move=> &1.
  proc; sp; if=> //; sp; match =; auto; smt().


+ proc.
  sp; if=> //.
  sp; match =; auto; smt(). 
+ move=> &2 ->.
  proc; sp; if=> //; sp; match =; auto; smt().
+ move=> &1.
  proc; sp; if=> //; sp; match =; auto; smt().
auto=> />.
move=> rl rr al bl dl pl sl ar br dr pr sr. 
by case : (!br) => />.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 2b: Bound the bad event. *)

lemma Step2b &m: Pr[E_GWAKE(Game2, A).run() @ &m : Game2.bad] <= ((q_m1 + q_m2 + q_m3) ^ 2)%r * mu1 dctxt (mode dctxt).
proof.
apply (StdOrder.RealOrder.ler_trans Pr[BD.Exp(BD.Sample, Red_Coll(A)).main() @ &m : ! uniq BD.Sample.l]); first last.
+ apply (BD.pr_collision_q2 (Red_Coll(A))).
  + move => S S_ll.
    islossless.
    apply (A_ll (Counter(Red_Coll_O_WAKE(S)))); islossless.
    + by match; auto; islossless.
    + match; auto. 
      by sp; match; auto; islossless.
    + match => //.
      by sp; match; auto; islossless.
    + match => //; islossless.
      by match; islossless.
    match => //; islossless.
    by match; islossless.
  proc; inline.
  sp.
  conseq (: _ ==> size BD.Sample.l <= Counter.cm1 + Counter.cm2 + Counter.cm3) (: Counter.cm1 = 0 /\ Counter.cm2 = 0 /\ Counter.cm3 = 0 ==> Counter.cm1 <= q_m1 /\ Counter.cm2 <= q_m2 /\ Counter.cm3 <= q_m3)=> //.
  + smt().
  + by call (A_bounded_qs (Red_Coll_O_WAKE(BD.Sample))).
  call (: size BD.Sample.l <= Counter.cm1 + Counter.cm2 + Counter.cm3) => //.
  + proc; inline*; if; auto.
  + proc; inline*; sp; if => //; auto => /#.
  + proc; inline*.
    sp; if => //.
    + case ((Red_Coll_O_WAKE.dec_map.[(a, b), msg1_data a b, ca]) = None).
      + match None ^match => //. 
        auto => /#.
      match Some ^match => //; auto => /#.
    auto => /#.
  + proc; inline*.
    sp; if => //.
    + sp; match; 2,3,4,5: auto => /#.
      case ((Red_Coll_O_WAKE.dec_map.[(a, s.`1), msg2_data a s.`1 s.`4, m2]) = None).
      + match None ^match => //.  
        + by auto => />.
        by auto => /#.
      by match Some ^match => //; auto => /#.
    auto => /#.
  + proc; inline*; auto => /#.
  + proc; inline*; auto => /#.
  + proc; inline*; auto => /#.
  auto => /#.
byequiv => //.
proc; inline.
call (:
 ={state_map, psk_map, bad, dec_map}(Game2, Red_Coll_O_WAKE(BD.Sample))
 /\ (Game2.bad{1} => !uniq BD.Sample.l{2})
 /\ (forall pk ad c, (pk, ad, c) \in Game2.dec_map{1} => c \in BD.Sample.l{2})
) => //.

+ by sim />.

+ proc; inline.
  sp; if=> //; auto=> />.
  smt(mem_set).

+ proc; inline.
  sp; if=> //; 2: by auto=> />.
  sp; match = => //.
  + by auto => />.
  move=> na.
  auto=> />.
  smt(mem_set).

+ proc; inline.
  sp; if=> //; 2: by auto=> />.
  sp; match =; auto=> />.
  + by auto=> /#.
  sp; match = => //.
  + by auto.
  move=> nb.
  auto=> />.
  smt(mem_set).

+ by sim />.

+ by sim />.

by sim />.

auto=> />.
smt(emptyE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 3: No longer store nonces in the state, just retrieve from the dec_map. *)

local op clear_nonces (s : instance_state) =
match s with
| IPending st m1 => 
  let (id, psk, na, ca) = st in IPending (id, psk, witness, ca) m1 
| RPending st m1 m2 => 
  let (id, psk, na, nb, ca, cb) = st in RPending (id, psk, witness, witness, ca, cb) m1 m2 
| Accepted _ _ => s
| Observed _ _ => s
| Aborted => s
end.

local lemma eq_partners_nonces h tr r sml smr: 
  (forall h, omap (fun (v: role * instance_state) => let (r, s) = v in (r, clear_nonces s)) sml.[h] = smr.[h]) =>
get_partners h tr r sml = get_partners h tr r smr.
proof.
move=> eqsm.
rewrite /get_partners.
congr.
apply fmap_eqP => h'.
rewrite !filterE -(eqsm h') /=. 
case: (sml.[h'])=> //=.
by move=> [r' []] // [] /= /#.
qed.

local lemma eq_obs_partners_nonces h sml smr: 
  (forall h, omap (fun (v: role * instance_state) => let (r, s) = v in (r, clear_nonces s)) sml.[h] = smr.[h]) =>
get_observed_partners h sml = get_observed_partners h smr.
proof.
move=> eqsm.
rewrite /get_observed_partners.
congr.
+ rewrite fun_ext => bj.
  rewrite -(eqsm bj) //=.
  case: (sml.[bj])=> //.
  by move=> [r' []] // [].
rewrite -(eq_partners_nonces _ _ _ sml smr eqsm). 
rewrite -(eqsm h) /s /r //=.
case: (sml.[h])=> //.
by move=> [r' []] // [].
qed.

lemma Step3 &m: Pr[E_GWAKE(Game3, A).run() @ &m : res] = Pr[E_GWAKE(Game4, A).run() @ &m :res].
proof.
byequiv (: ={glob A} ==> _) => //.
proc; inline*.
call(: ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
    /\ (forall a i, Game3_inv Game3.state_map Game3.dec_map a i){1}
).

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_gen_pskey _ => //.
  proc.
  by if; auto.

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_send_msg1 _ => //.
  proc; inline*.
  sp; if=> //.
  + smt().
  seq 1 1 : (#pre /\ ={ca}); 1: by auto.  
  sp; if=> //.
  sp; seq 1 1 : (#pre /\ ={na}); 1: by auto=> />.
  auto=> />.
  smt(get_setE).

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_send_msg2 _ => //.
  proc; inline*.
  sp; if=> //.
  + smt().
  match = => //.
  + by auto; smt(get_setE).
  move=> na.
  seq 1 1 : (#pre /\ ={cb}); 1: by auto.
  sp; if=> //.
  auto=> />.
  smt(get_setE).

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_send_msg3 _ => //.
  proc; inline*.
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 2..5: by auto.
  move=> sl m1l sr m1r.
  sp; match = => //.
  + smt().
  + by auto; smt(get_setE).
  move=> nb.
  seq 1 1 : (#pre /\ ={caf}); 1: by auto.
  sp; if=> //.
  auto=> />.
  move=> &1 &2 bad <- dm smr sml inv invl aiin nbad ok _.
  by case: (invl a{2} i{2}); smt(get_setE).

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_send_fin _ => //.
  proc; inline*.
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,3..5: by auto.
  move=> sl m1l m2l sr m1r m2r.
  sp; match = => //.
  + smt().
  + by auto; smt(get_setE).
  move=> nok.
  auto=> />.
  move=> &1 &2 <- dm smr sml inv /(_ b{2} j{2}) []; smt(get_setE).

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_rev_skey _ => //.
  proc; inline. 
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,2,5: by auto.
  + move=> tr k tr' k'.
    sp ^if & -1 ^if & -1; if=> //.
    + smt(eq_partners_nonces).
    sp ^if & -1 ^if & -1; if.
    + move=> /> &1 &2 smr sml eqsm.
      by rewrite (eq_obs_partners_nonces (a, i){2} Game3.state_map{1} Game4.state_map{2}).
    + seq 1 1 : (={ps, p} /\ #pre).
      + auto=> /> &1 &2 smr sml eqsm.
        by rewrite (eq_obs_partners_nonces (a, i){2} Game3.state_map{1} Game4.state_map{2}).
      wp 2 2.
      conseq (: _ ==> ={k, role} /\ tr = tr').
      + move=> /> &1 &2 _ + + eqsm invl a_in _ _.
        rewrite -(eqsm (a, i){2}).
        by case: (Game3.state_map{1}.[(a, i){2}]); smt(get_setE).
      auto=> /> &1 &2 + + + eqsm invl a_in _ _.
      rewrite -(eqsm (a, i){2}) -(eqsm p{2}).
      case: (Game3.state_map{1}.[(a, i){2}])=> />.
      + by case: (Game3.state_map{1}.[p{2}])=> /#.
      by case: (Game3.state_map{1}.[p{2}])=> /#.
    auto=> /> &1 &2 + + eqsm invl a_in _ _.
    rewrite -(eqsm (a, i){2}).
    by case: (Game3.state_map{1}.[(a, i){2}]); smt(get_setE).
  by auto; smt().

- conseq (: ={res}
    /\ ={psk_map, bad, dec_map}(Game3, Game4)
    /\ (forall h, omap (fun v => let (r, s) = v in (r, clear_nonces s)) Game3.state_map.[h]{1} = Game4.state_map.[h]{2})
  ) Game3_inv_test _ => //.
  proc; inline. 
  sp; if=> //.
  + smt().
  sp; match; 1..5: smt(); 1,2,5: by auto.
  + move=> tr k tr' k'.
    sp ^if & -1 ^if & -1; if=> //.
    + smt(eq_partners_nonces).
    sp ^if & -1 ^if & -1; if.
    + move=> /> &1 &2 smr sml eqsm.
      by rewrite (eq_obs_partners_nonces (a, i){2} Game3.state_map{1} Game4.state_map{2}).
    + seq 1 1 : (={ps, p} /\ #pre).
      + auto=> /> &1 &2 smr sml eqsm.
        by rewrite (eq_obs_partners_nonces (a, i){2} Game3.state_map{1} Game4.state_map{2}).
      wp 2 2.
      conseq (: _ ==> ={k, role} /\ tr = tr').
      + move=> /> &1 &2 _ + + eqsm invl a_in _ _.
        rewrite -(eqsm (a, i){2}).
        by case: (Game3.state_map{1}.[(a, i){2}]); smt(get_setE).
      auto=> /> &1 &2 + + + eqsm invl a_in _ _.
      rewrite -(eqsm (a, i){2}) -(eqsm p{2}).
      case: (Game3.state_map{1}.[(a, i){2}])=> />.
      + by case: (Game3.state_map{1}.[p{2}])=> /#.
      by case: (Game3.state_map{1}.[p{2}])=> /#.
    auto=> /> &1 &2 + + eqsm invl a_in _ _.
    rewrite -(eqsm (a, i){2}).
    by case: (Game3.state_map{1}.[(a, i){2}]); smt(get_setE).
  by auto; smt().
 
auto=> />.
split; 1: smt(emptyE).
move=> a i.
exact /Game3_undef/emptyE.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 4: Delay the sampling of na and nb until msg3, sampling them together. *)

local clone import DProd.ProdSampling with
  type t1 <- nonce,
  type t2 <- nonce
proof *.

lemma Step4 &m: Pr[E_GWAKE(Game4, A).run() @ &m : res] = Pr[E_GWAKE(Game5, A).run() @ &m : res].
byequiv => //.
proc*.
outline {1} [1] { r <@ MainD(Red_ROM(A), RO).distinguish(); }.

+ inline*.
  wp.
  call (: ={state_map, psk_map, bad}(Game4, Red_ROM.WAKE_O)
       /\ (forall h, h \in Game4.dec_map{1} <=> h \in Red_ROM.WAKE_O.dec_map{2})
       /\ (forall c ad n, (exists pk, Game4.dec_map{1}.[(pk, ad, c)] = Some n) <=> RO.m{2}.[(ad, c)] = Some n)
       /\ (forall a b ca cb, ((a, b), msg2_data a b ca, cb) \in Game4.dec_map => ((a, b), msg1_data a b, ca) \in Game4.dec_map){1}
       /\ (forall a b ca cb caf, ((a, b), msg3_data a b ca cb, caf) \in Game4.dec_map => ((a, b), msg2_data a b ca, cb) \in Game4.dec_map){1}
  ) => //.

  - by proc; sp; if; auto.

  - proc; inline*.
    sp; if=> //.
    seq 1 1 : (#pre /\ ={ca}); 1: by auto.
    sp; if=> //.
    + smt().
    + rcondt {2} ^if; 1: by auto=> /#. 
      auto=> />.
      smt(get_setE).
    by auto=> /#.
  
   - proc; inline*.
     sp; if=> //. 
     match; 1,2: smt().
     + by auto=> />.
     move=> nal nar.
     seq 1 1 : (#pre /\ ={cb}); 1: by auto.
     sp; if=> //.
     + smt().
     + rcondt {2} ^if; 1: by auto=> /#. 
       auto=> />.
       smt(get_setE).
     by auto=> /#.

   - proc; inline*.
     sp; if=> //. 
     sp; match = => //.
     + smt().
     move=> s m1.
     sp; match; 1,2: smt().
     + by auto=> />.
     move=> nbl nbr.
     seq 1 1 : (#pre /\ ={caf}); 1: by auto.
     sp; if=> //.
     + smt().
     + rcondt {2} ^if; 1: by auto=> /#.
       rcondf {2} ^if.
       + auto=> />.
         smt(mem_set).
       rcondf {2} ^if.
       + auto=> />.
         smt(mem_set).
       swap {2} ^r1<$ @ ^ok<-.
       seq 1 1 : (#pre /\ ok{1} = r1{2}); 1: by auto => />.
       auto=> />.
       smt(get_setE).
    by auto=> /#.
  
   - proc; inline*.
     sp; if=> //. 
     sp; match = => //.
     + smt().
     move=> s m1 m2.
     sp; match; 1,2: smt().
     + by auto=> />.
     move=> nokl nokr.
     rcondf {2} ^if; 1: by auto=> /#.
     rcondf {2} ^if; 1: by auto=> /#.
     auto=> />.
     smt(get_setE).
  
   - by sim />.
   
   - by sim />.

   auto=> />.
   smt(emptyE).
  
have ll : forall (c : msg_data * ctxt), is_lossless dnonce by move=> _; exact dnonce_ll.
rewrite equiv [{1} 1 (FullEager.RO_LRO (Red_ROM(A)) ll)].
inline*.
wp; call (: 
  ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  /\ (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map){2}
) => //.

- by sim />.

- conseq (: ={res}
  /\ ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  ) _ Game5_inv_send_msg1 => //.
  proc; inline*.
  sp; if=> //.
  by auto=> />.

- conseq (: ={res}
  /\ ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  ) _ Game5_inv_send_msg2 => //.
  proc; inline*.
  sp; if=> //.
  by sp; match =; auto=> />.

- conseq (: ={res}
  /\ ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  ) _ Game5_inv_send_msg3 => //.
  proc; inline*.
  sp; if=> //.
  sp; match = => //.
  + smt().
  move=> s m1.
  sp; match = => //.
  + by auto.
  move=> nb.
  seq 1 1 : (#pre /\ ={caf}); 1: by auto.
  sp; if=> //.
  rcondt {1} ^if.
  + auto=> />.
    move=> &hr _ dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 /domE/some_oget sms /negb_or [_ cafnin] r _. 
    rewrite -sm in sms.
    case: (invr5 a{m0} i{m0}); rewrite sms //=.
    move=> /> 4!->> _.
    exact inv1.
  rcondt {1} ^if.
  + auto=> />.
    move=> &hr _ dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 /domE/some_oget sms /negb_or [_ cafnin] r _ r1 _. 
    rewrite -sm in sms.
    case: (invr5 a{m0} i{m0}) ; rewrite sms //=.
    move=> /> 4!->> _.
    rewrite mem_set /#.
  outline {2} [3] (na, nb') <@ S.sample. 
  wp; rewrite equiv [{2} 3 sample_sample2].
  inline*.
  auto=> />.
  move=> &1 &2 _ dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 /domE/some_oget sms /negb_or [_ cafnin] r _ r1 _. 
  rewrite get_set_sameE //=.
  rewrite -sm in sms.
  case: (invr5 a{2} i{2}); rewrite sms //=.
  smt(get_setE).

- conseq (: ={res}
  /\ ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  ) _ Game5_inv_send_fin => //.
- proc; inline*.
  sp; if=> //.
  sp; match = => //.
  + smt().
  move=> s m1 m2.
  sp; match = => //.
  + by auto.
  move=> nok.
  rcondf {1} ^if.
  + auto=> />.
    move=> &hr dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 /domE/some_oget sms r _.
    rewrite -sm in sms.
    case: (invr5 b{m0} j{m0}) ; rewrite sms //=.
    smt().
  rcondf {1} ^if.
  + auto=> />.
    move=> &hr dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 /domE/some_oget sms r _ r2 _.
    rewrite -sm in sms.
    case: (invr5 b{m0} j{m0}) ; rewrite sms //=.
    smt().
  auto=> />.
  smt().

- conseq (: ={res}
  /\ ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  ) _ Game5_inv_rev_skey => //.
  by sim />.

- conseq (: ={res}
  /\ ={state_map, psk_map, bad, dec_map}(Red_ROM.WAKE_O, Game5)
  /\ (forall a b ca, (forall cb caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg1_data a b, ca) \notin RO.m{1})
  /\ (forall a b ca cb, (forall caf, (msg3_data a b ca cb, caf) \notin Game5.prfkey_map{2})
        => (msg2_data a b ca, cb) \notin RO.m{1})
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in Game5.prfkey_map{2} =>
         exists na nb, Game5.prfkey_map{2}.[(msg3_data a b ca cb, caf)] = Some (na, nb) /\
                       RO.m{1}.[(msg1_data a b, ca)] = Some na /\
                       RO.m{1}.[(msg2_data a b ca, cb)] = Some nb)
  ) _ Game5_inv_test => //.
  by sim />.

auto => />.
smt(emptyE Game5_undef).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 5: Apply the PRF assumption. *)


lemma Step5 &m:
    `|Pr[E_GWAKE(Game5, A).run() @ &m : res] - Pr[E_GWAKE(Game6, A).run() @ &m : res]|
  = 
    `|Pr[E_GPRF(PRF0, Red_PRF(A)).run() @ &m : res] - Pr[E_GPRF(PRF1, Red_PRF(A)).run() @ &m : res]|.
proof.
do! congr.
+ byequiv => //.
  proc; inline*.
  wp.
  call (:
        ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
     /\ (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map){1}
  )=> //.

  - by sim />.

  - conseq (: ={res}
     /\ ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
    ) Game5_inv_send_msg1 _ => //.
    by sim />.

  - conseq (: ={res}
     /\ ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
    ) Game5_inv_send_msg2 _ => //.
    by sim />.

  - conseq (: ={res}
     /\ ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
    ) Game5_inv_send_msg3 _ => //.
    proc; inline*.
    sp; if=> //. 
    sp; match = => //.
    + smt().
    move=> s m1.
    sp; match =.
    + smt().
    + by auto=> />.
    move=> nb.
    seq 1 1 : (#pre /\ ={caf}); 1: by auto.
    sp; if=> //.
    rcondt{2} ^if.
    + auto=> />. 
      smt().
    match Some {2} ^match.
    + by auto => />; smt(mem_set).
    auto => />. 
    smt(get_setE).

  - conseq (: ={res}
     /\ ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
    ) Game5_inv_send_fin _ => //.
     proc; inline*.
     sp; if=> //. 
     sp; match = => //.
     + smt().
     move=> s m1 m2.
     sp; match =.
     + smt().
     + by auto=> />.
     move=> nok.
     match Some {2} ^match.
     + auto=> />.
       smt().
     auto => />.
     smt(get_setE).

  - conseq (: ={res}
     /\ ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
    ) Game5_inv_rev_skey _ => //.
    by sim />.

  - conseq (: ={res}
     /\ ={psk_map, state_map, dec_map, bad}(Game5, Red_PRF.WAKE_O)
     /\ ={prfkey_map}(Game5, PRFb)
    ) Game5_inv_test _ => //.
    by sim />.

  auto => />.
  smt(emptyE Game5_undef).

byequiv => //.
proc; inline *.
wp.
call (:
      ={psk_map, state_map, dec_map, bad}(Game6, Red_PRF.WAKE_O)
   /\ ={prfkey_map}(Game6, PRFb)
   /\ (forall a b m1 m2 m3, ((a, b), msg3_data a b m1 m2, m3) \in Game6.dec_map{1} <=> ((msg3_data a b m1 m2, m3), (a, b)) \in PRF1.cache{2})
   /\ (forall a b m1 m2 m3 k, PRF1.cache.[((msg3_data a b m1 m2, m3), (a, b))]{2} = Some k => Game6.sk_map.[((a, m1), m2, m3)]{1} = Some k)
   /\ (forall a b m1 m2 m3, ((a, b), msg3_data a b m1 m2, m3) \in Game6.dec_map <=> (msg3_data a b m1 m2, m3) \in Game6.prfkey_map){1}
)=> //. 

- by sim />.

- proc; inline*. 
  sp; if => //.
  auto => />.
  smt(get_setE).

- proc; inline*.
  sp; if => //.
  match = => //.
  + by auto => />. 
  auto => />.
  smt(get_setE).

- proc; inline*.
  sp; if=> //. 
  sp; match = => //.
  + smt().
  move=> s m1.
  sp; match =.
  + smt().
  + by auto=> />.
  move=> nb.
  seq 1 1 : (#pre /\ ={caf}); 1: by auto.
  sp; if=> //.
  rcondt{2} ^if.
  + auto=> />.
    smt().
  match Some {2} ^match.
  + auto=> />.
    smt(get_setE). 
  rcondt{2} ^if.
  + auto => />.
    smt().
  auto=> />.
  smt(get_setE).

- proc; inline*.
  sp; if=> //. 
  sp; match = => //.
  + smt().
  move=> s m1 m2.
  sp; match =.
  + smt().
  + by auto=> />.
  move=> nok.
  match Some {2} ^match.
  + auto=> />.
    smt().
  rcondf{2} ^if.
  + auto => />.
    smt().
  auto=> />.
  smt().

- by sim />.

- by sim />.

auto => />.
smt(emptyE).
qed.
