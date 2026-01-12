require import AllCore FMap FSet Distr NSL List.
import GAKEc AEADc.

(* ------------------------------------------------------------------------------------------ *)
(* Intermediate Games *)
(* ------------------------------------------------------------------------------------------ *)

(* Inlining and removing psk from instance state *)
module Game1 = {
  var b0 : bool

  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap

  proc init_mem(b: bool) : unit = {
    b0 <- b;
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

  proc send_msg1(a, i, b) = {
    var na, ca;
    var mo <- None;

    if ((a, i) \notin state_map /\ (a, b) \in psk_map) {
      na <$ dnonce;
      ca <$ enc (oget psk_map.[(a, b)]) (msg1_data a b) na;
      mo <- Some ca;
      state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, oget mo) (a, oget mo));
    }
    return mo;
  }

  proc send_msg2(b, j, m1) = {
    var a, ca, role, st, nb, cb;
    var mo <- None;

    (a, ca) <- m1;
    (role, st) <- oget state_map.[(b, j)];
    if ((b, j) \notin state_map /\ (a, b) \in psk_map) {
      if (dec (oget psk_map.[(a, b)]) (msg1_data a b) ca is Some na) {
        nb <$ dnonce;
        cb <$ enc (oget psk_map.[(a, b)]) (msg2_data a b ca) nb;
        mo <- Some cb;
        state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, oget mo) m1 (oget mo));
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
        if (dec (oget psk_map.[(a, b)]) (msg2_data a b ca) m2 is Some nb) {
          ok <$ dnonce;
          caf <$ enc (oget psk_map.[(a, b)]) (msg3_data a b ca m2) ok;
          mo <- Some caf;
          skey <- prf (na, nb) (a, b);
          state_map.[(a, i)] <- (Initiator, Accepted ((a, ca), m2, oget mo) skey);
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
        if (dec (oget psk_map.[(a, b)]) (msg3_data a b ca cb) m3 is Some nok) {
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

  proc reveal(a, i) = {
    var role, st, ps, k;
    var ko <- None;

    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      match st with
      | Accepted trace k' => {
        ps <- get_observed_partners (a, i) state_map;
        if (card ps = 0) {
          k <- k';
          ko <- Some k;
          state_map.[(a, i)] <- (role, Observed trace k);
        }
      }
      | Observed _ _   => { }
      | IPending _ _   => { }
      | RPending _ _ _ => { }
      | Aborted        => { }
      end;
    }
    return ko;
  }

  proc test(a, i) = {
    var role, st, ps, k;
    var ko <- None;

    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      match st with
      | Accepted trace k' => {
        ps <- get_observed_partners (a, i) state_map;
        if (card ps = 0) {
          if (b0 = false) {
            k <- k';
          } else {
            k <$ dskey;
          }
          ko <- Some k;
          state_map.[(a, i)] <- (role, Observed trace k);
        }
      }
      | Observed _ _   => { }
      | IPending _ _   => { }
      | RPending _ _ _ => { }
      | Aborted        => { }
      end;
    }
    return ko;
  }
}.

(* Decmap instead of real enc/dec *)
module Game2 = Game1 with {
  var dec_map: ((id * id) * msg_data * ctxt, nonce) fmap
  var bad : bool

  proc init_mem [
    -1 + { dec_map <- empty; bad <- false; }
  ]

  proc send_msg1 [
    ^if.^na<$ -
    ^if.^ca<$ ~ {
      ca <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, ca) \in dec_map;
      na <$ dnonce;
      dec_map.[((a,b), msg1_data a b, ca)] <- na;
     }
  ]

  proc send_msg2 [
    ^if.^match ~ (dec_map.[((a, b), msg1_data a b, ca)])
    ^if.^match#Some.^nb<$ -
    ^if.^match#Some.^cb<$ ~ {
      cb <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, cb) \in dec_map;
      nb <$ dnonce;
      dec_map.[((a,b), msg2_data a b ca, cb)] <- nb;
     }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match ~ (dec_map.[((a, b), msg2_data a b ca, m2)])
    ^if.^match#IPending.^match#Some.^ok<$ -
    ^if.^match#IPending.^match#Some.^caf<$ ~ {
      caf <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, caf) \in dec_map;
      ok <$ dnonce;
      dec_map.[((a,b), msg3_data a b ca m2, caf)] <- ok;
     }
  ]
  proc send_fin [
    ^if.^match#RPending.^match ~ (dec_map.[((a, b), msg3_data a b ca cb, m3)])
  ]
}.

(* No ctxt collisions *)
module Game3 = Game2 with {
  proc send_msg1 [
    [^if.^bad<- - ^state_map<-] + (!bad)
  ]

  proc send_msg2 [
    [^if.^match#Some.^bad<- - ^state_map<-] + (!bad)
  ]

  proc send_msg3 [
    [^if.^match#IPending.^match#Some.^bad<- - ^state_map<-] + (!bad)
  ]
}.

(* Simplify nonce retrieval *)
module Game4 = Game3 with {
  proc send_msg1 [
    ^if.^if.^state_map<- ~ {
      state_map.[(a, i)] <- (Initiator, IPending (b, witness, witness, ca) (a, ca));
    }
  ]

  proc send_msg2 [
    ^if.^match#Some.^if.^state_map<- ~ {
      state_map.[(b, j)] <- (Responder, RPending (a, witness, witness, witness, ca, cb) m1 cb);
    }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ {
      skey <- prf (oget (dec_map.[((a, b), msg1_data a b, ca)]), nb) (a, b);
    }
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- prf (oget (dec_map.[((a, b), msg1_data a b, ca)]), oget (dec_map.[((a, b), msg2_data a b ca, cb)])) (a, b);
    }
  ]
}.

(* Delay nonce sampling *)
module Game5 = Game4 with {
  var prfkey_map : (msg_data * ctxt, nonce * nonce) fmap

  proc init_mem [
    -1 + { prfkey_map <- empty; }
  ]

  proc send_msg1 [
    ^if.^if.^na<$ -
    ^if.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg1_data a b, ca)] <- witness;
    }
  ]

  proc send_msg2 [
    ^if.^match#Some.^if.^nb<$ -
    ^if.^match#Some.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg2_data a b ca, cb)] <- witness;
    }
  ]

  proc send_msg3 [
    var nb' : nonce
    ^if.^match#IPending.^match#Some.^if.^ok<$ -
    ^if.^match#IPending.^match#Some.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg3_data a b ca m2, caf)] <- witness;
    }
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ {
      (na, nb') <$ dnonce `*` dnonce;
      prfkey_map.[(msg3_data a b ca m2, caf)] <- (na, nb');
      skey <- prf (na, nb') (a, b);
    }
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- prf (oget prfkey_map.[(msg3_data a b ca cb, m3)]) (a, b);
    }
  ]
}.

module Game6 = Game5 with {
  var sk_map : (trace, skey) fmap

  proc init_mem [
    -1 + { sk_map <- empty; }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ {
       skey <$ dskey;
       sk_map.[((a, ca), m2, caf)] <- skey;
    }
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- oget sk_map.[((a, ca), cb, m3)];
    }
  ]
}.

module Game7 = Game6 with {
  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^sk_map<- + { skey <- witness; }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ { skey <- witness; }
  ]
  proc reveal [
    ^if.^match#Accepted.^if.^k<- ~ {
      k <- oget sk_map.[trace];
    }
  ]
  proc test [
    ^if.^match#Accepted.^if.^if.^k<- ~ {
      k <- oget sk_map.[trace];
    }
  ]
}.

module Game8 = Game7 with {
  proc send_msg3 [
    [^if.^match#IPending.^match#Some.^if.^skey<$ - ^sk_map<-] -
  ]

  proc reveal [
    var k'' : skey

    ^if.^match#Accepted.^if.^k<- ~ {
      k'' <$ dskey;
      if (trace \notin sk_map) {
        sk_map.[trace] <- k'';
      }
      k <- oget Game8.sk_map.[trace];
    }
  ]

  proc test [
    var k'' : skey

    ^if.^match#Accepted.^if.^if ~ {
      k'' <$ dskey;
      if (trace \notin sk_map) {
        sk_map.[trace] <- k'';
      }
      if (b0 = false) {
        k <- oget Game8.sk_map.[trace];
      } else {
        k <$ dskey;
      }
    }
  ]
}.
(* ------------------------------------------------------------------------------------------ *)
(* Game 0 invariants *)

op GAKEb_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
  (* Pending session state relation to psk map and well formedness of messages *)
  (forall a i r b psk na c1 m1, sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
   => pskm.[a, b] = Some psk /\ m1 = (a, c1))
  /\ (forall a i r b psk na nb c1 c2 m1 m2, sm.[a, i] = Some (r, RPending (b, psk, na, nb, c1, c2) m1 m2)
   => pskm.[b, a] = Some psk /\ m1 = (b, c1) /\ m2 = c2).

hoare GAKEb_inv_gen_pskey: GAKEb(NSL).gen_pskey:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proof.
proc; inline *.
if => //.
auto => /> *.
by split; smt(get_setE).
qed.

hoare GAKEb_inv_send_msg1: GAKEb(NSL).send_msg1:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proc; inline *.
sp; if => //.
auto => />.
smt(get_setE).
qed.

hoare GAKEb_inv_send_msg2: GAKEb(NSL).send_msg2:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ match None ^match; 1: by auto.
  auto => />.
  smt(get_setE).
match Some ^match; 1: by auto=> /#.
auto => /> &m decn st inv1 inv2 bjnin /domE abin n _ cb0 cin.
smt(get_setE).
qed.

hoare GAKEb_inv_send_msg3: GAKEb(NSL).send_msg3:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: by auto.
sp; match.
- match None ^match; 1: by auto.
  auto => />.
  smt(get_setE).
match Some ^match; 1: auto => /#.
auto => />.
smt(get_setE).
qed.

hoare GAKEb_inv_send_fin: GAKEb(NSL).send_fin:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
- match None ^match; 1: by auto.
  auto => />.
  smt(get_setE).
match Some ^match; 1: auto => /#.
auto => />.
smt(get_setE).
qed.

hoare GAKEb_inv_reveal: GAKEb(NSL).reveal:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
auto => />.
smt(get_setE).
qed.

hoare GAKEb_inv_test: GAKEb(NSL).test:
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i)
==>
    (forall a i, GAKEb_inv GAKEb.state_map GAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
if => //.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1 invariants *)

op Game1_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
  (* Pending session state relation to psk map and well formedness of messages *)
  (forall a i r b psk na c1 m1, sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
   => (a, b) \in pskm /\ m1 = (a, c1))
  /\ (forall a i r b psk na nb c1 c2 m1 m2, sm.[a, i] = Some (r, RPending (b, psk, na, nb, c1, c2) m1 m2)
   => (b, a) \in pskm /\ m1 = (b, c1) /\ m2 = c2).

hoare Game1_inv_gen_pskey: Game1.gen_pskey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
wp; if => //.
auto => />.
smt(mem_set).
qed.

hoare Game1_inv_send_msg1: Game1.send_msg1:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_send_msg2: Game1.send_msg2:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_send_msg3: Game1.send_msg3:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_send_fin: Game1.send_fin:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_reveal: Game1.reveal:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_test: Game1.test:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
if => //.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 2 invariants *)

hoare Game2_inv_gen_pskey: Game2.gen_pskey:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.gen_pskey ~ Game1.gen_pskey: ={arg} /\ ={state_map, psk_map}(Game2, Game1) ==> ={state_map, psk_map}(Game2, Game1)] by sim />.
by conseq t Game1_inv_gen_pskey=> /#.
qed.

hoare Game2_inv_send_msg1: Game2.send_msg1:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
auto => />.
smt(get_setE).
qed.

hoare Game2_inv_send_msg2: Game2.send_msg2:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game2_inv_send_msg3: Game2.send_msg3:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game2_inv_send_fin: Game2.send_fin:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game2_inv_reveal: Game2.reveal:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.reveal ~ Game1.reveal: ={arg} /\ ={state_map, psk_map}(Game2, Game1) ==> ={state_map, psk_map}(Game2, Game1)] by sim />.
by conseq t Game1_inv_reveal => /#.
qed.

hoare Game2_inv_test: Game2.test:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.test ~ Game1.test: ={arg} /\ ={b0, state_map, psk_map}(Game2, Game1) ==> ={b0, state_map, psk_map}(Game2, Game1)] by sim />.
by conseq t Game1_inv_test => /#.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 3 invariants *)

op Game3_inv (sm: (id * int, role * instance_state) fmap) (dm : ((id * id) * msg_data * ctxt, nonce) fmap) (a: id) (i: int) =
  (* Pending session state relation to dec map and well formedness of messages *)
  (forall a i r b psk na c1 m1, sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
      => dm.[((a, b), msg1_data a b, c1)] = Some na
      /\ m1 = (a, c1))
  /\ (forall a i r b psk na nb c1 c2 m1 m2, sm.[a, i] = Some (r, RPending (b, psk, na, nb, c1, c2) m1 m2)
      => dm.[((b, a), msg1_data b a, c1)] = Some na
      /\ dm.[((b, a), msg2_data b a c1, c2)] = Some nb
      /\ m1 = (b, c1) /\ m2 = c2).

hoare Game3_inv_gen_pskey: Game3.gen_pskey:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
wp; if => //.
by auto.
qed.

hoare Game3_inv_send_msg1: Game3.send_msg1:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp; if => //.
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto => />.
smt(get_setE).
qed.

hoare Game3_inv_send_msg2: Game3.send_msg2:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match.
+ auto => />.
  smt(get_setE).
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto => />.
smt(get_setE).
qed.

hoare Game3_inv_send_msg3: Game3.send_msg3:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => />.
  smt(get_setE).
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto => />.
smt(get_setE).
qed.

hoare Game3_inv_send_fin: Game3.send_fin:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1: auto; 2..4: auto.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game3_inv_reveal: Game3.reveal:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => />.
smt(get_setE).
qed.

hoare Game3_inv_test: Game3.test:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
if => //.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 5 invariants *)

op Game5_inv
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (nm : (msg_data * ctxt, nonce * nonce) fmap)
=
  (* Unicity of pending initiators *)
  ((forall a i j c r r' b b' psk psk' na na' m1 m1',
       sm.[(a, i)] = Some (r, IPending (b, psk, na, c) m1)
    /\ sm.[(a, j)] = Some (r', IPending (b', psk', na', c) m1')
    => i = j)

  (* Pending initiator state relationships *)
  /\ (forall a i r b psk na c1 m1,
        sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
        => ((a, b), msg1_data a b, c1) \in dm
        /\ forall c2 c3, (msg3_data a b c1 c2, c3) \notin nm)

  (* Ordering of messages in the log *)
  /\ (forall a b ca cb, ((a, b), msg2_data a b ca, cb) \in dm => ((a, b), msg1_data a b, ca) \in dm)
  /\ (forall a b ca cb caf, ((a, b), msg3_data a b ca cb, caf) \in dm => ((a, b), msg2_data a b ca, cb) \in dm)

  (* Log and nonce map equivalence *)
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in nm <=> ((a, b), msg3_data a b ca cb, caf) \in dm)).

hoare Game5_inv_send_msg1: Game5.send_msg1:
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp; if=> //.
seq 1 : (#pre); 1: by auto.
case (Game5.bad).
+ by rcondf ^if; auto=> />.
auto=> />.
move => &m *.
do split; ~1: smt(get_setE).
move => a0 i0 j c r r' b0 b' psk psk' na0 na' m1 m1'.
rewrite !get_setE.
case ((a0, i0) = (a, i){m}).
+ case ((a0, j) = (a, i){m}) => //.
  smt(get_setE).
case ((a0, j) = (a, i){m}) => //. 
+ move => />.
  smt(get_setE).
smt().
qed.

hoare Game5_inv_send_msg2: Game5.send_msg2:
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp; if=> //.
sp; match => //.
+ auto=> />.
  smt(get_setE).
seq 1 : (#pre); 1: by auto.
auto=> />.
smt(mem_set get_setE).
qed.

hoare Game5_inv_send_msg3: Game5.send_msg3:
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  smt(get_setE).
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto=> />.
smt(mem_set get_setE).
qed.

hoare Game5_inv_send_fin: Game5.send_fin:
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp ^if; if=> //.
sp; match => //.
sp; match; auto; smt(get_setE).
qed.

hoare Game5_inv_reveal: Game5.reveal:
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto=> />.
smt(get_setE).
qed.

hoare Game5_inv_test: Game5.test:
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
if; auto; smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 8 invariants *)

(* Return the first sent message from a state *)
op fst_msg s : ctxt option =
with s = IPending _ m1   => Some m1.`2
with s = RPending _ m1 m2 => Some m1.`2
with s = Accepted t _   => Some t.`1.`2
with s = Observed t _   => Some t.`1.`2
with s = Aborted    => None.

(* Return the second sent message from a state *)
op snd_msg s : ctxt option =
with s = IPending _ m1   => None
with s = RPending _ m1 m2 => Some m2
with s = Accepted t _   => Some t.`2
with s = Observed t _   => Some t.`2
with s = Aborted    => None.

op Game8_inv
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (skm : (trace, skey) fmap)
=
(* Unicity of pending initiators *)
   (forall h h' c r b psk na m1 st',
    sm.[h] = Some (r, IPending (b, psk, na, c) m1)
    /\ sm.[h'] = Some (r, st')
    /\ fst_msg st' = Some c
    => h = h')

(* Unicity of pending responders *)
/\ (forall h h' c1 c r b psk na nb m1 m2 st',
    sm.[h] = Some (r, RPending (b, psk, na, nb, c1, c) m1 m2)
    /\ sm.[h'] = Some (r, st')
    /\ snd_msg st' = Some c
    => h = h')

(* Unicity of completed sessions with same trace and role *)
/\ (forall t h h' r s s',
    sm.[h] = Some (r, s) /\ sm.[h'] = Some (r, s')
    /\ get_trace s = Some t /\ get_trace s' = Some t
    => h = h' /\ s = s')

(* Session state and log relationships *)
/\ (forall a i r b psk na c1 m1,
      sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
      => ((a, b), msg1_data a b, c1) \in dm /\ r = Initiator /\ m1 = (a, c1))

/\ (forall a i r b psk na nb c1 c2 m1 m2,
      sm.[a, i] = Some (r, RPending (b, psk, na, nb, c1, c2) m1 m2)
      => ((b, a), msg1_data b a, c1) \in dm /\ ((b, a), msg2_data b a c1, c2) \in dm
      /\ r = Responder /\ m1 = (b, c1) /\ c2 = m2)

/\ (forall a i r b m1 m2 m3 sk,
      sm.[a, i] = Some (r, Accepted ((b, m1), m2, m3) sk)
      => (exists pk ad, (pk, ad, m1) \in dm) /\ (exists pk ad, (pk, ad, m2) \in dm))

/\ (forall a i r b m1 m2 m3 sk,
      sm.[a, i] = Some (r, Observed ((b, m1), m2, m3) sk)
      => (exists pk ad, (pk, ad, m1) \in dm) /\ (exists pk ad, (pk, ad, m2) \in dm))

(* SK implies existence of an observed session *)
/\ (forall t, t \in skm => exists a i r k, sm.[a, i] = Some (r, Observed t k)).

hoare Game8_inv_send_msg1: Game8.send_msg1:
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp; if=> //.
seq 1 : (#pre); 1: by auto.
auto => />.
move => &m uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs sm psk bad.
do! split; ~1:smt(get_setE).
move => h h' c r b' psk' na' m1 st'.
rewrite !get_setE.
case (h = (a, i){m}).
+ case (h' = (a, i){m}) => //.
  smt(get_setE).
case (h' = (a, i){m}) => //. 
+ move => />.
  smt(get_setE).
smt().
qed.

hoare Game8_inv_send_msg2: Game8.send_msg2:
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp; if=> //.
sp; match => //.
+ auto=> />.
  move => &m dm sm uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs smnin pskin.
  do! split; smt(get_setE).
seq 1 : (#pre); 1: by auto.
auto => />.
move => &m dm sm uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs smnin pskin bad.
do! split; ~2: smt(get_setE).
move => h h' c1 c r b' psk' na' nb' m1' m2 st'.
rewrite !get_setE.
case (h = (b, j){m}).
+ case (h' = (b, j){m}) => //.
  smt(get_setE).
case (h' = (b, j){m}) => //. 
+ move => />.
  smt(get_setE).
smt().
qed.

hoare Game8_inv_send_msg3: Game8.send_msg3:
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp; if=> //.
sp; match => //.
sp; match => //.
+ auto => />.
  move => &m dm sm uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs smin.
  do! split; smt(get_setE).
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto=> />.
move => &m _ dm sm uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in /negb_or [_ uniq] nab _.
do! split; ~6:smt(get_setE).
move => v x r b' m1' m2' m3' sk.
rewrite get_setE.
by case ((v, x) = (a, i){m}); smt(get_setE).
qed.

hoare Game8_inv_send_fin: Game8.send_fin:
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  move => *.
  do! split; smt(get_setE).
auto => />.
move => &m dm sm uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in.
do! split; ~6:smt(get_setE).
move => v x r b' m1' m2' m3' sk.
rewrite get_setE.
by case ((v, x) = (b, j){m}) => /#.
qed.

hoare Game8_inv_reveal: Game8.reveal:
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
rcondt ^if.
+ auto => />.
  move => &m smai uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps k _.
  case (trace{m} \in Game8.sk_map{m}) => // ^ tr_in_skm.
  move => /(sk_obs trace{m}) [a' i' r sk smai'].
  have := uniq_comp trace{m} (a, i){m} (a', i') role{m} (Accepted trace{m} k'{m}) (Observed trace{m} sk).
  have -> : Game8.state_map{m}.[a{m}, i{m}] = Some (role{m}, Accepted trace{m} k'{m}) by smt().
  rewrite smai' some_oget //=.
  case (r = role{m}) => //.
  move => neq_role.
  have bj_partner : (a', i') \in get_partners (Some trace{m}) role{m} Game8.state_map{m}.
  + rewrite /get_partners mem_fdom mem_filter /#.
  have // : (a', i') \in get_observed_partners (a, i){m} Game8.state_map{m}.
  + rewrite /get_observed_partners in_filter /#.
  rewrite fcard_eq0 in obs_ps.
  by rewrite obs_ps in_fset0.
auto => />.
move => &m smai uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps k _.
do! split; ~7,8: smt(get_setE).
+ move => a0 i0 r b m1 m2 m3 sk.
  rewrite get_setE.
  by case ((a0, i0) = (a, i){m}) => /#.
move => t.
rewrite mem_set.
case; smt(get_setE).
qed.

hoare Game8_inv_test: Game8.test:
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
rcondt ^if.
+ auto => />.
  move => &m smai uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps k _.
  case (trace{m} \in Game8.sk_map{m}) => // ^ tr_in_skm.
  move => /(sk_obs trace{m}) [a' i' r sk smai'].
  have := uniq_comp trace{m} (a, i){m} (a', i') role{m} (Accepted trace{m} k'{m}) (Observed trace{m} sk).
  have -> : Game8.state_map{m}.[a{m}, i{m}] = Some (role{m}, Accepted trace{m} k'{m}) by smt().
  rewrite smai' some_oget //=.
  case (r = role{m}) => //.
  move => neq_role.
  have bj_partner : (a', i') \in get_partners (Some trace{m}) role{m} Game8.state_map{m}.
  + rewrite /get_partners mem_fdom mem_filter /#.
  have // : (a', i') \in get_observed_partners (a, i){m} Game8.state_map{m}.
  + rewrite /get_observed_partners in_filter /#.
  rewrite fcard_eq0 in obs_ps.
  by rewrite obs_ps in_fset0.
seq 1 : #pre; 1: by auto => />.
sp.
seq 1 : #pre; 1: by auto => />.
sp.
auto => />.
move => &m sm smai uniq_pi uniq_pr uniq_comp ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps _.
do! split; ~7,8: smt(get_setE).
+ move => a0 i0 r b m1 m2 m3 sk.
  rewrite get_setE.
  by case ((a0, i0) = (a, i){m}) => /#.
move => t.
rewrite mem_set.
case; smt(get_setE).
qed.
