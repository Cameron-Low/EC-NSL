require import AllCore FSet FMap Distr DProd PROM NSL Games.
import GWAKEc AEADc PRFc.

(* ------------------------------------------------------------------------------------------ *)
(* Reductions *)
(* ------------------------------------------------------------------------------------------ *)

print Game1.
(* AEAD Reduction *)
module (Red_AEAD (D : A_GWAKE) : A_GAEAD) (O : GAEAD_out) = {
  (*
  module WAKE_O : GWAKE_out = Game1 with {
    var - psk_map
    
    proc init_mem [ ^psk_map<- - ]
    proc gen_pskey ~ O.gen
    proc send_msg1
    (ex : bool)
    [
      ^mo<- + { ex <@ O.ex((a, b)); },
      ^if ~ ((a, i) \notin state_map /\ ex),
      ^if.^ca<$ -,
      ^if.^mo<- ~ { mo <@ O.enc((a, b), msg1_data a b, na); ca <- oget mo; }
    ]
    
  }
  *)
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
            state_map.[(a, i)] <- (Initiator, Accepted (m1, m2, oget mo) skey);
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
            state_map.[(b, j)] <- (Responder, Accepted (m1, m2, m3) skey);
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
      },
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
              O.gen(caf);
              skey <@ O.f(caf, (a, b));
              state_map.[a, i] <- (Initiator, Accepted (m1, m2, caf) (oget skey));
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
            skey <@ O.f(m3, (a, b));
            state_map.[b, j] <- (Responder, Accepted (m1, m2, m3) (oget skey));
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
          (* Get partners *)
          ps <- get_partners (a, i) (Some trace) role state_map;
          if (card ps <= 1) {
            ps <- get_observed_partners (a, i) state_map;
            (* If we have no observed partners then, we can test *)
            if (card ps <> 0) {
              (* If a partner has revealed something, we must use the same key *)
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
(* Security Proof *)
(* ------------------------------------------------------------------------------------------ *)
section.

declare module A <: A_GWAKE {-GWAKE0, -Game1, -Game2, -Game3, -Game4, -Game5, -Game6, -GAEAD0, -GAEAD1, -PRF0, -PRF1, -Red_AEAD, -Red_ROM, -Red_PRF, -RO, -FRO}.

declare axiom A_ll:
forall (GW <: GWAKE_out{-A}),
  islossless GW.gen_pskey =>
  islossless GW.send_msg1 =>
  islossless GW.send_msg2 =>
  islossless GW.send_msg3 =>
  islossless GW.send_fin =>
  islossless GW.rev_skey => islossless GW.test => islossless A(GW).run.


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
  )=> //; 1,2,3,6,7: sim />.
  
  - proc; inline*.
    sp; if=> //. 
    sp; match = => //.
    + smt().
    move=> s m1.
    sp; match; 1,2: smt().
    + by auto=> />.
    move=> nbl nbr.
    seq 1 1 : (#pre /\ ={caf}); 1: by auto.
    case (Game5.bad{1}).
    + rcondf {1} ^if; 1: by auto=> />.
      rcondf {2} ^if; 1: by auto=> />.
      by auto=> />.
    sp; if=> //.
    sp; if{2} => //.
    + match Some {2} ^match. auto => />. smt(mem_set).
      auto => /> &1 &2 dmr badr dmnr dmnl smr sml aiin _ nindm ninprfm.
      smt(get_setE).
    match Some {2} ^match. auto => />. smt().
    auto => />. 
    admit. (* using uniqueness of caf to argue that update on left doesn't happen *)

   - proc; inline*.
     sp; if=> //. 
     sp; match = => //.
     + smt().
     move=> s m1 m2.
     sp; match; 1,2: smt().
     + by auto=> />.
     move=> nokl nokr.
     sp 0 3; match{2}.
     + auto => /> &1 &2 prfn _ _ _ _ _. 
       congr. rewrite prfn oget_none. 
       admit. (* axiom that prf with witness as key returns witness? *)
     auto => />.
     smt(get_setE).

  auto => />.

byequiv => //.
proc; inline *.
wp.
call (:
      ={psk_map, state_map, dec_map, bad}(Game6, Red_PRF.WAKE_O)
   /\ ={prfkey_map}(Game6, PRFb)
   /\ ={cache}(Game6, PRF1)
)=> //; 1,2,3,6,7: sim />. 

- proc; inline*.
  sp; if=> //. 
  sp; match = => //.
  + smt().
  move=> s m1.
  sp; match; 1,2: smt().
  + by auto=> />.
  move=> nbl nbr.
  seq 1 1 : (#pre /\ ={caf}); 1: by auto.
  case (Game6.bad{1}).
  + rcondf {1} ^if; 1: by auto=> />.
    rcondf {2} ^if; 1: by auto=> />.
    by auto=> />.
  sp; if=> //.
  sp; if{2} => //.
  + match Some {2} ^match. auto => />. smt(mem_set).
    seq 1 1 : (#pre /\ (na, ok){1} = k{2}). auto => />. admit.
    sp.
    seq 1 1 : (#pre /\ skey{1} = y{2}); 1: by auto => />.
    if => //.
    - smt(get_setE).
    - auto => /> &1 &2 prfk _ _ _ _ _ _ _ _ _; smt(get_setE).
    auto => /> &1 &2 prfk ? ? ? ? ? ? ? _ ? _ _. admit. (* I have stored right key *)
  match Some {2} ^match. auto => /#.
  admit.

- proc; inline*.
  sp; if=> //. 
  sp; match = => //.
  + smt().
  move=> s m1 m2.
  sp; match; 1,2: smt().
  + by auto=> />.
  move=> nokl nokr.
  sp 0 3; match{2}.
  + auto => /> &1 &2 prfn _ _ _ _ _. 
    congr. 
    admit.
  auto => /> &1 &2 prfk _ _ smr sml bjin y0 _.
  split. admit.
  admit.

auto => />.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Step 0: Inline procedure calls, and remove pskeys from the state using psk_map to retrieve. *)

local op clear_psk (s : instance_state) =
match s with
| IPending st m1 => 
  let (id, psk, na, ca) = st in IPending (id, witness, na, ca) m1 
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
    move=> &1 &2 smr sml inv_sm invl ai_in.
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
    match Some {2} ^match.
    + auto=> />.
      move=> &hr smr sml invl ai_in.
      by case: (invl a{m0} i{m0})=> /#.
    sp; match =.
    + by auto=> /#. 
    + by auto=> /#.
    move=> nb.
    match Some {2} ^match.
    + auto=> /> &1 decl decr smr sml invl ai_in ok _.
      by case: (invl a{m0} i{m0})=> /#.
    by auto=> /#.

  - conseq (: ={res}
         /\ ={psk_map}(Game1, GAEADb)
         /\ ={state_map}(Game1, Red_AEAD.WAKE_O)
    ) Game1_inv_send_fin _ => //.
    proc; inline.
    sp; if=> //.
    sp; match = => //.
    + smt().
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
(* Step 2: Remove collisions of all produced ciphertexts. *)

lemma Step2 &m: `| Pr[E_GWAKE(Game2, A).run() @ &m : res] - Pr[E_GWAKE(Game3, A).run() @ &m : res] | <= Pr[E_GWAKE(Game3, A).run() @ &m : Game3.bad].
proof.
byequiv (: _ ==> _) : Game2.bad => //; first last.
+ move=> &1 &2.
  by case: (Game3.bad{2}).
proc; inline*.
call (: Game3.bad, ={bad, psk_map, state_map, dec_map}(Game2, Game3), ={bad}(Game2, Game3)) => //.
+ exact A_ll.

+ by proc; inline*; auto; if; auto.
+ move=> &2 ->.
  proc; sp; if; auto.
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
  move=> &1 &2 <- dm smr sml inv invl aiin h.
  by case: (invl b{2} j{2}); smt(get_setE).

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
transitivity* {1} { r <@ MainD(Red_ROM(A), RO).distinguish(); } => //.
+ smt().

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
     case (Game4.bad{1}).
     + rcondf {1} ^if; 1: by auto=> />.
       rcondf {2} ^if; 1: by auto=> />.
       by auto=> />.
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
  seq 1 1 : (#pre /\ ={ca}); 1: by auto.
  case (Game5.bad{2}).
  + rcondf {1} ^if; 1: by auto=> />.
    rcondf {2} ^if; 1: by auto=> />.
    auto=> />.
  sp 1 1; if=> //.
  auto=> />.

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
  sp; match = => //.
  + by auto=> />.
  move=> na.
  seq 1 1 : (#pre /\ ={cb}); 1: by auto.
  case (Game5.bad{2}).
  + rcondf {1} ^if; 1: by auto=> />.
    rcondf {2} ^if; 1: by auto=> />.
    auto=> />.
  sp 1 1; if=> //.
  auto=> />.

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
  case (Game5.bad{2}).
  + rcondf {1} ^if; 1: by auto=> />.
    rcondf {2} ^if; 1: by auto=> />.
    auto=> />.
  sp 1 1; if=> //.
  rcondt {1} ^if.
  + auto=> />.
    move=> &hr _ dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 aiin _ cafnin r _. 
    have sms : (Game5.state_map.[(a, i)] = Some (role, IPending (b, psk, na, ca) m1)){m0} by smt().
    case: (invr5 a{m0} i{m0}) ; rewrite sms //=.
    move=> /> 4!->> _.
    exact inv1.
  rcondt {1} ^if.
  + auto=> />.
    move=> &hr _ dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 aiin _ cafnin r _ r1 _. 
    have sms : (Game5.state_map.[(a, i)] = Some (role, IPending (b, psk, na, ca) m1)){m0} by smt().
    case: (invr5 a{m0} i{m0}) ; rewrite sms //=.
    move=> /> 4!->> _.
    rewrite mem_set /#.
  outline {2} [3] (na, ok) <@ S.sample. 
  wp; rewrite equiv [{2} 3 sample_sample2].
  inline*.
  auto=> />.
  move=> &1 &2 _ dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 aiin _ cafnin r _ r1 _. 
  rewrite get_set_sameE //=.
  have smai : (Game5.state_map.[(a, i)] = Some (role, IPending (b, psk, na, ca) m1)){2} by smt().
  case: (invr5 a{2} i{2}); rewrite smai //=.
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
    move=> &hr dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 bjin r _.
    have sms : (Game5.state_map.[(b, j)] = Some (role, RPending (a, psk, na, nb, ca, cb) m1 m2)){m0} by smt().
    case: (invr5 b{m0} j{m0}) ; rewrite sms //=.
    smt().
  rcondf {1} ^if.
  + auto=> />.
    move=> &hr dm _ sm _ inv1 inv2 inv3 invr1 invr2 invr3 invr4 invr5 bjin r _ r2 _.
    have sms : (Game5.state_map.[(b, j)] = Some (role, RPending (a, psk, na, nb, ca, cb) m1 m2)){m0} by smt().
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
