require import AllCore Distr FSet FMap.
require GWAKE Aead.

type id, pskey, skey, nonce, ctxt.
type ids = id * id.

(* Additional data for AEAD *)
type msg_data =
[ msg1_data of id & id
| msg2_data of id & id & ctxt
| msg3_data of id & id & ctxt & ctxt
].

(* Distributions over types *)
op dpskey : pskey distr.
op [lossless] dskey : skey distr.
op dctxt : ctxt distr.
op [lossless] dnonce : nonce distr.

(* Construction operators *)
op enc : pskey -> msg_data -> nonce -> ctxt distr.
op dec : pskey -> msg_data -> ctxt -> nonce option.
op prf : nonce * nonce -> id * id -> skey.

(* Type of the messages sent between parties in the protocol *)
type trace = (id * ctxt) * ctxt * ctxt.

(* Represents the state of a party in the protocol *)
type istate = id * pskey * nonce * ctxt.
type rstate = id * pskey * nonce * nonce * ctxt * ctxt.

clone import GWAKE as GWAKEc with
  type id <- id,
  type msg <- ctxt,
  type key <- skey,
  type pskey <- pskey,
  type istate <- istate,
  type rstate <- rstate,
  op dkey <- dskey,
  op dpskey <- dpskey.
  
clone import Aead as AEADc with
  type handle  <- ids,
  type key         <- pskey,
  type data        <- msg_data,
  type ptxt        <- nonce,
  type ctxt        <- ctxt,
    op dkey        <- dpskey,
    op dctxt       <- dctxt,
    op enc         <- enc,
    op dec         <- dec
proof *.
realize correctness by admit. (** TODO: Lift the axiom up **)

(* The Protocol *)
(*
  The protocol doesn't handle any state itself (it is state-passing).
  Instead it relies on the game to handle it.
*)
module NSL : AKE_Scheme = {
  proc msg1(a : id, b : id, psk : pskey) : (id * ctxt) * istate = {
    var na, ca;
    na <$ dnonce;
    ca <$ enc psk (msg1_data a b) na;
    return ((a, ca), (b, psk, na, ca));
  }

  proc msg2(b: id, m1: id * ctxt, psk: pskey) : (ctxt * rstate) option = {
    var a, ca, n, nb, cb;
    var r <- None;

    (a, ca) <- m1;
    n <- dec psk (msg1_data a b) ca;
    if (n is Some na) {
      nb <$ dnonce;
      cb <$ enc psk (msg2_data a b ca) nb;
      r <- Some (cb, (a, psk, na, nb, ca, cb));
    }
    return r;
  }

  proc msg3(a : id, s: istate, cb: ctxt) : (ctxt * skey) option = {
    var psk, b, na, ca, ok, skey, nbo, caf;
    var r <- None;

    (b, psk, na, ca) <- s;
    nbo <- dec psk (msg2_data a b ca) cb;
    if (nbo <> None) {
      skey <- prf (na, oget nbo) (a, b);
      ok <$ dnonce;
      caf <$ enc psk (msg3_data a b ca cb) ok;
      r <- Some (caf, skey);
    }

    return r;
  }

  proc fin(b : id, s: rstate, caf: ctxt) : skey option = {
    var a, psk, na, nb, ca, cb, ok, skey;
    var r <- None;

    (a, psk, na, nb, ca, cb) <- s;
    ok <- dec psk (msg3_data a b ca cb) caf;
    if (ok <> None) {
      skey <- prf (na, nb) (a, b);
      r <- Some skey;
    }
    return r;
  }
}.

(* Reductions *)

module (Red_AEAD (D : A_GWAKE) : A_GAEAD) (O : GAEAD_out) = {
  module WAKE_O : GWAKE_out = {
    var state_map: (id * int, role * instance_state) fmap
  
    proc init_mem() : unit = {
      state_map <- empty;
    }
  
    proc gen_pskey = O.gen
  
    proc init(a, i, r, b) = {
      var ex, na;
      var mo <- None;
  
      ex <@ O.ex((a, b));
      if (ex) {
        if (r = Initiator) {
          na <$ dnonce;
          mo <@ O.enc((a, b), msg1_data a b, na);
          state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, oget mo) (b, oget mo));
        } else {
          state_map.[(a, i)] <- (Responder, RStarted b);
        }
      }
      return (mo);
    }


    proc send_msg2(b, j, m1) = {
      var a, ca, role, st, n, nb;
      var mo <- None;
  
      (a, ca) <- m1;
      (role, st) <- oget state_map.[(b, j)];
      if (st = RStarted a) {
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
          if (ok <> None) {
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
              (p_role, p_st) <- oget GWAKEb.state_map.[p];
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
        | RStarted _     => { }
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

(* Games *)

module GWAKE_ideal_aead = {
  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap
  var dec_map: (pskey * msg_data * ctxt, nonce) fmap

  proc init_mem() : unit = {
    state_map <- empty;
    psk_map <- empty;
  }

  proc gen_pskey(a: id, b: id) : unit = {
    var k;
    if ((a, b) \notin psk_map) {
      k <$ dpskey;
      psk_map.[(a, b)] <- k;
    }
  }
  
  proc init(a, i, r, b) = {
    var na, ca;
    var mo <- None;
 
    if ((a, b) \in psk_map) {
      if (r = Initiator) {
        na <$ dnonce;
        ca <$ dctxt;
        mo <- Some ca;
        dec_map.[(oget psk_map.[(a,b)], msg1_data a b, ca)] <- na;
        state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, ca) (b, ca));
      } else {
        state_map.[(a, i)] <- (Responder, RStarted b);
      }
    }
    return mo;
  }


  proc send_msg2(b, j, m1) = {
    var a, ca, role, st, nb, cb;
    var mo <- None;
 
    (a, ca) <- m1;
    (role, st) <- oget state_map.[(b, j)];
    if (st = RStarted a) {
      if (dec_map.[(oget psk_map.[(a, b)], msg1_data a b, ca)] is Some na) {
        nb <$ dnonce;
        cb <$ dctxt;
        mo <- Some cb;
        dec_map.[(oget psk_map.[(a,b)], msg2_data a b ca, cb)] <- nb;
        state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, cb) m1 cb);
      } else {
        state_map.[(b, j)] <- (Responder, Aborted);
      }
    }
    return mo;
  }

  proc send_msg3(a, i, m2) = {
    var role, st, b, psk, na, ca, skey, ok, caf;
    var mo <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      if (st is IPending s m1) {
        (b, psk, na, ca) <- s;
        if (dec_map.[(oget psk_map.[(a, b)], msg2_data a b ca, m2)] is Some nb) {
          skey <- prf (na, nb) (a, b);
          ok <$ dnonce;
          caf <$ dctxt;
          mo <- Some caf;
          dec_map.[(oget psk_map.[(a,b)], msg3_data a b ca m2, caf)] <- ok;
          state_map.[(a, i)] <- (Initiator, Accepted (m1, m2, caf) skey);
         } else {
          state_map.[(a, i)] <- (Initiator, Aborted);
        }
      }
    }
    return mo;
  }

  proc send_fin(b, j, m3) = {
    var role, st, a, psk, na, nb, ca, cb, skey;
    var mo <- None;

    if ((b, j) \in state_map) {
      (role, st) <- oget state_map.[(b, j)];
      if (st is RPending s m1 m2) {
        (a, psk, na, nb, ca, cb) <- s;
        if (dec_map.[(oget psk_map.[(a, b)], msg3_data a b ca cb, m3)] <> None) {
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
            (p_role, p_st) <- oget GWAKEb.state_map.[p];
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
      | RStarted _     => { }
      | Aborted        => { }
      end;
    }
    return ko;
  }
 
  proc test = rev_skey
}.

(*
module GWAKE_nocol = {
  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap
  var dec_map: (pskey * msg_data * ctxt, nonce) fmap

  proc init_mem() : unit = {
    state_map <- empty;
    psk_map <- empty;
  }

  proc gen_pskey(a: id, b: id) : unit = {
    var k;
    if ((a, b) \notin psk_map) {
      k <$ dpskey;
      psk_map.[(a, b)] <- k;
    }
  }
  
  proc init(a, i, r, b) = {
    var na, ca;
    var mo <- None;
 
    if ((a, b) \in psk_map) {
      if (r = Initiator) {
        na <$ dnonce;
        ca <$ dctxt;
        if (forall pk ad, (pk, ad, ca) \notin dec_map) {
          mo <- Some ca;
          dec_map.[(oget psk_map.[(a,b)], msg1_data a b, ca)] <- na;
          state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, ca) (b, ca));
        }
      } else {
        state_map.[(a, i)] <- (Responder, RStarted b);
      }
    }
    return mo;
  }


  proc send_msg2(b, j, m1) = {
    var a, ca, role, st, nb, cb;
    var mo <- None;
 
    (a, ca) <- m1;
    (role, st) <- oget state_map.[(b, j)];
    if (st = RStarted a) {
      if (dec_map.[(oget psk_map.[(a, b)], msg1_data a b, ca)] is Some na) {
        nb <$ dnonce;
        cb <$ dctxt;
        if (forall pk ad, (pk, ad, cb) \notin dec_map) {
          mo <- Some cb;
          dec_map.[(oget psk_map.[(a,b)], msg2_data a b ca, cb)] <- nb;
          state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, cb) m1 cb);
        }
      } else {
        state_map.[(b, j)] <- (Responder, Aborted);
      }
    }
    return mo;
  }

  proc send_msg3(a, i, m2) = {
    var role, st, b, psk, na, ca, skey, ok, caf;
    var mo <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      if (st is IPending s m1) {
        (b, psk, na, ca) <- s;
        if (dec_map.[(oget psk_map.[(a, b)], msg2_data a b ca, m2)] is Some nb) {
          caf <$ dctxt;
          mo <- Some caf;
          if (forall pk ad, (pk, ad, caf) \notin dec_map) {
            ok <$ dnonce;
            dec_map.[(oget psk_map.[(a,b)], msg3_data a b ca m2, caf)] <- ok;
            skey <- prf (na, nb) (a, b);
            state_map.[(a, i)] <- (Initiator, Accepted (m1, m2, caf) skey);
          }
        } else {
          state_map.[(a, i)] <- (Initiator, Aborted);
        }
      }
    }
    return mo;
  }

  proc send_fin(b, j, m3) = {
    var role, st, a, psk, na, nb, ca, cb, skey;
    var mo <- None;

    if ((b, j) \in state_map) {
      (role, st) <- oget state_map.[(b, j)];
      if (st is RPending s m1 m2) {
        (a, psk, na, nb, ca, cb) <- s;
        if (dec_map.[(oget psk_map.[(a, b)], msg3_data a b ca cb, m3)] <> None) {
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
            (p_role, p_st) <- oget GWAKEb.state_map.[p];
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
      | RStarted _     => { }
      | Aborted        => { }
      end;
    }
    return ko;
  }
 
  proc test = rev_skey
}.

module GWAKE_move_ns = {
  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap
  var dec_map: (pskey * msg_data * ctxt, nonce) fmap
  var nonce_map: (ctxt, nonce) fmap

  proc init_mem() : unit = {
    state_map <- empty;
    psk_map <- empty;
  }

  proc gen_pskey(a: id, b: id) : unit = {
    var k;
    if ((a, b) \notin psk_map) {
      k <$ dpskey;
      psk_map.[(a, b)] <- k;
    }
  }
  
  proc init(a, i, r, b) = {
    var na, ca;
    var mo <- None;
 
    if ((a, b) \in psk_map) {
      if (r = Initiator) {
        na <$ dnonce;
        ca <$ dctxt;
        if (forall pk ad, (pk, ad, ca) \notin dec_map) {
          mo <- Some ca;
          dec_map.[(oget psk_map.[(a,b)], msg1_data a b, ca)] <- na;
          state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, ca) (b, ca));
        }
      } else {
        state_map.[(a, i)] <- (Responder, RStarted b);
      }
    }
    return mo;
  }


  proc send_msg2(b, j, m1) = {
    var a, ca, role, st, nb, cb;
    var mo <- None;
 
    (a, ca) <- m1;
    (role, st) <- oget state_map.[(b, j)];
    if (st = RStarted a) {
      if (dec_map.[(oget psk_map.[(a, b)], msg1_data a b, ca)] is Some na) {
        nb <$ dnonce;
        cb <$ dctxt;
        if (forall pk ad, (pk, ad, cb) \notin dec_map) {
          mo <- Some cb;
          dec_map.[(oget psk_map.[(a,b)], msg2_data a b ca, cb)] <- nb;
          state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, cb) m1 cb);
        }
      } else {
        state_map.[(b, j)] <- (Responder, Aborted);
      }
    }
    return mo;
  }

  proc send_msg3(a, i, m2) = {
    var role, st, b, psk, na, nb, ca, skey, ok, caf;
    var mo <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      if (st is IPending s m1) {
        (b, psk, na, ca) <- s;
        if (dec_map.[(oget psk_map.[(a, b)], msg2_data a b ca, m2)] is Some nb) {
          ok <$ dnonce;
          caf <$ dctxt;
          if (forall pk ad, (pk, ad, caf) \notin dec_map) {
            mo <- Some caf;
            if (nonce_map.[ca] = None) {
              na <$ dnonce;
              nonce_map.[ca] <- na;
            }
            if (nonce_map.[m2] = None) {
              nb <$ dnonce;
              nonce_map.[m2] <- nb;
            }
            na <- oget nonce_map.[ca];
            nb <- oget nonce_map.[m2];
            skey <- prf (na, nb) (a, b);
            dec_map.[(oget psk_map.[(a,b)], msg3_data a b ca m2, caf)] <- ok;
            state_map.[(a, i)] <- (Initiator, Accepted (m1, m2, caf) skey);
          }
        } else {
          state_map.[(a, i)] <- (Initiator, Aborted);
        }
      }
    }
    return mo;
  }

  proc send_fin(b, j, m3) = {
    var role, st, a, psk, na, nb, ca, cb, skey;
    var mo <- None;

    if ((b, j) \in state_map) {
      (role, st) <- oget state_map.[(b, j)];
      if (st is RPending s m1 m2) {
        (a, psk, na, nb, ca, cb) <- s;
        if (dec_map.[(oget psk_map.[(a, b)], msg3_data a b ca cb, m3)] <> None) {
          na <- oget nonce_map.[m1.`2];
          nb <- oget nonce_map.[m2];
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
            (p_role, p_st) <- oget GWAKEb.state_map.[p];
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
      | RStarted _     => { }
      | Aborted        => { }
      end;
    }
    return ko;
  }
 
  proc test = rev_skey
}.
*)


section.

declare module A <: A_GWAKE {-GWAKE0, -GWAKE_ideal_aead, -GAEAD0, -GAEAD1, -Red_AEAD }.

local op state_equality (i: int) (sm1 sm2 : (int, id * role * instance_state) fmap) =
  match sm1.[i] with
  | None => i \notin sm2
  | Some v1 =>
    match sm2.[i] with
    | None => false
    | Some v2 =>
      v1 = v2 (* FIXME: equality on all but `psk` *)
    end
  end.

lemma Step1 &m:
    `|Pr[E_GWAKE(GWAKE0(NSL), A).run() @ &m : res] - Pr[E_GWAKE(GWAKE_ideal_aead, A).run() @ &m : res]|
  = 
    `|Pr[E_GAEAD(GAEAD0, Red_AEAD(A)).run() @ &m : res] - Pr[E_GAEAD(GAEAD1, Red_AEAD(A)).run() @ &m : res]|.
proof.
do! congr.
+ byequiv => //.
  proc; inline*.
  wp.
  call (:
       ={psk_map}(GWAKEb, GAEADb)
    /\ ={cnt}(GWAKEb, Red_AEAD.WAKE_O)
    /\ (forall i, state_equality i GWAKEb.state_map{1} Red_AEAD.WAKE_O.state_map{2})
    /\ (forall i a b, Red_AEAD.WAKE_O.state_map.[i] = Some (b, Responder, RStarted a) => (a, b) \in GAEADb.psk_map){2}
  ).
  + proc.
    if; auto. smt(get_setE).
  + proc; inline.
    sp; if=> //. 
    sp; if => //. 
    - match Some {2} 6. auto => /#.
      auto => />. 
      admit.
    auto => /> &1 &2 A B C D E. split. smt(get_setE). 
    move => i a1 b1. rewrite get_setE //=.
    
  + proc; inline.
    sp; if => //. smt().
    match Some {2} 5. auto => /> &m1 E F G H. 
    rewrite -fmapP.
apply (H j{m0} _ _ role{m0}). rewrite E.
    exists  

smt(get_setE).    

    sp; match => //. admit. admit. admit. admit. admit. admit.
    move => a psk a' psk'.
    match Some {2} 5. auto => />.

    sp; match =. smt().
    sp; if => //. smt().
    sp. match Some {2} 1. auto => />. smt(get_setE).
match =.

admitted.
  

lemma Step2 &m:
    `|Pr[E_GWAKE(GWAKE_ideal_aead, A).run() @ &m : res] - Pr[E_GWAKE(GWAKE_ideal_aead_nc, A).run() @ &m : res]|
  <=
    BB.


lemma Step3
