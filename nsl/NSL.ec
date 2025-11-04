require import AllCore Distr FSet FMap.
require GAKE Aead PRF.

type id, pskey, skey, nonce, ctxt.
type ids = id * id.

(* Additional data for AEAD *)
type msg_data =
[ msg1_data of id & id
| msg2_data of id & id & ctxt
| msg3_data of id & id & ctxt & ctxt
].

(* Distributions over types *)
op [lossless] dpskey : pskey distr.
op [lossless] dskey : skey distr.
op [lossless] dctxt : ctxt distr.
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

axiom correctness k ad p c: k \in dpskey => c \in enc k ad p => dec k ad c = Some p.

clone import GAKE as GAKEc with
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
  type d_in_t  <- bool,
  type key         <- pskey,
  type data        <- msg_data,
  type ptxt        <- nonce,
  type ctxt        <- ctxt,
    op dkey        <- dpskey,
    op dctxt       <- dctxt,
    op enc         <- enc,
    op dec         <- dec,
    axiom correctness <- correctness
proof *.

clone import PRF as PRFc with 
  type handle <- msg_data * ctxt,
  type d_in_t <- bool,
  type key    <- nonce * nonce,
  type D      <- ids,
  type R      <- skey, 
  op   dkey   <- dnonce `*` dnonce,
  op   dR _   <- dskey,
  op   f      <- prf
proof *.

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
    if (nbo is Some nb) {
      skey <- prf (na, nb) (a, b);
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
    if (ok is Some nok) {
      skey <- prf (na, nb) (a, b);
      r <- Some skey;
    }
    return r;
  }
}.
