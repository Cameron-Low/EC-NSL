require import AllCore FSet FMap NSL Games.
import GWAKEc AEADc.

(* Reductions *)

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
      return (mo);
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
    GAEAD1.ctxts <- empty;
    b <@ D(WAKE_O).run();
    return b;
  }
}.

section.

declare module A <: A_GWAKE {-GWAKE0, -Game1, -Game2, -GAEAD0, -GAEAD1, -Red_AEAD }.

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
  by match Some {1} 5; auto; smt(get_setE).

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
  + match None {1} 2; auto; smt(get_setE).
  move=> nb.
  match Some {1} 6.
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
  + match None {1} 2; auto; smt(get_setE).
  move=> nb.
  match Some {1} 4.
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
  by rcondt{2} ^if; auto.

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
  by rcondt {2} ^if; auto.

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
  sp; match =.
  + by auto.
  + by auto.
  move=> nok.
  by auto.

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

auto=> />.
move=> a i.
exact /Game1_undef/emptyE.
qed.
