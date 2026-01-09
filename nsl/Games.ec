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
        state_map.[(b, j)] <- (Responder, Aborted R1);
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
          state_map.[(a, i)] <- (Initiator, Aborted (I ca));
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
          state_map.[(b, j)] <- (Responder, Aborted (R2 ca cb));
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
      | Aborted  _     => { }
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
      | Aborted  _     => { }
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
smt(get_setE).
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

(* Return the messages from a state *)
op get_msgs s : ctxt list =
with s = Accepted t _   => [t.`1.`2; t.`2; t.`3]
with s = Observed t _   => [t.`1.`2; t.`2; t.`3]
with s = IPending _ m1   => [m1.`2]
with s = RPending _ m1 m2 => [m1.`2; m2]
with s = Aborted v  =>
  match v with
  | R1 => []
  | I m1 => [m1]
  | R2 m1 m2 => [m1; m2]
end.

inductive Game8_inv
  (sm: (id * int, role * instance_state) fmap)
  (skm : (trace, skey) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (a: id) (i: int)
=
| Game8_undef of
    (sm.[a, i] = None)
| Game8_aborted_r1 of
    (sm.[a, i] = Some (Responder, Aborted R1))
| Game8_aborted_i b c1 of
    (sm.[a, i] = Some (Initiator, Aborted (I c1)))
  & (((a, b), msg1_data a b, c1) \in dm)
| Game8_aborted_r2 b c1 c2 of
    (sm.[a, i] = Some (Responder, Aborted (R2 c1 c2)))
  & (((b, a), msg2_data b a c1, c2) \in dm)
| Game8_ipending b c1 of
    (sm.[a, i] = Some (Initiator, IPending (b, witness, witness, c1) (a, c1)))
  & (((a, b), msg1_data a b, c1) \in dm)
  & (forall c2 c3, ((a, b), msg3_data a b c1 c2, c3) \notin dm)
| Game8_rpending b c1 c2 of
    (sm.[a, i] = Some (Responder, RPending (b, witness, witness, witness, c1, c2) (b, c1) c2))
  & (((b, a), msg2_data b a c1, c2) \in dm)
| Game8_accepted_i b j st c1 c2 c3 of
    (sm.[a, i] = Some (Initiator, Accepted ((a, c1), c2, c3) witness))
  & (((a, b), msg3_data a b c1 c2, c3) \in dm)
  & (sm.[b, j] = Some (Responder, st))
  & (c1 \in get_msgs st /\ c2 \in get_msgs st)
  & (c3 \in get_msgs st <=> get_trace st <> None)
  & (!is_observed st => ((a, c1), c2, c3) \notin skm)
| Game8_accepted_r b j st c1 c2 c3 of
    (sm.[a, i] = Some (Responder, Accepted ((b, c1), c2, c3) witness))
  & (((b, a), msg3_data b a c1 c2, c3) \in dm)
  & (sm.[b, j] = Some (Initiator, st))
  & (get_trace st = Some ((b, c1), c2, c3))
  & (!is_observed st => ((b, c1), c2, c3) \notin skm)
| Game8_observed r id1 id2 c1 c2 c3 k of
    (sm.[a, i] = Some (r, Observed ((id1, c1), c2, c3) k))
  & (((id1, id2), msg3_data id1 id2 c1 c2, c3) \in dm)
  & (((id1, c1), c2, c3) \in skm)
  & (a = id1 \/ a = id2).

inductive Game8_inv_dm
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (c : ctxt)
=
| Game8_dm_undef of
    (forall a b, ((a, b), msg1_data a b, c) \notin dm)
  & (forall a b c1, ((a, b), msg2_data a b c1, c) \notin dm)
  & (forall a b c1 c2, ((a, b), msg3_data a b c1 c2, c) \notin dm)
| Game8_dm_m1 a b i st of
    (((a, b), msg1_data a b, c) \in dm)
  & (sm.[a, i] = Some (Initiator, st))
  & (c \in get_msgs st)
  & (forall h st',
       sm.[h] = Some (Initiator, st') =>
       c \in get_msgs st' =>
       h = (a, i))
| Game8_dm_m2 a b j st c1 of
    (((a, b), msg1_data a b, c1) \in dm)
  & (((a, b), msg2_data a b c1, c) \in dm)
  & (sm.[b, j] = Some (Responder, st))
  & (c1 \in get_msgs st)
  & (c \in get_msgs st)
  & (forall h st',
       sm.[h] = Some (Responder, st') =>
       c1 \in get_msgs st' =>
       c \in get_msgs st' =>
       h = (b, j))
| Game8_dm_m3 a b i st c1 c2 of
    (((a, b), msg1_data a b, c1) \in dm)
  & (((a, b), msg2_data a b c1, c2) \in dm)
  & (((a, b), msg3_data a b c1 c2, c) \in dm)
  & (sm.[a, i] = Some (Initiator, st))
  & (c1 \in get_msgs st)
  & (c2 \in get_msgs st)
  & (c \in get_msgs st)
  & (forall h st',
       sm.[h] = Some (Initiator, st') =>
       c1 \in get_msgs st' =>
       c2 \in get_msgs st' =>
       c \in get_msgs st' =>
       h = (a, i))
.

op Game8_inv_full
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (skm : (trace, skey) fmap)
=
  (forall a i, Game8_inv sm skm dm a i)
  /\ (forall c, Game8_inv_dm sm dm c)
  /\ (forall pk ad pk' ad' c,
        (pk, ad, c) \in dm =>
        (pk', ad', c) \in dm =>
        (pk, ad) = (pk', ad'))
  /\ (forall a c1 c2 c3, ((a, c1), c2, c3) \in skm => exists b, ((a, b), msg3_data a b c1 c2, c3) \in dm).

hoare Game8_inv_send_msg1: Game8.send_msg1:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp; if=> //.
seq 1 : (#pre); 1: by auto.
auto=> />.
move=> &m inv1 inv2 inv3 inv4 ai_nin_sm ab_in_psk bad.
do! split.

(* State Map invariant *)
move => a' i'.
case: ((a', i') = (a, i){m}) => /> => [| neq].
+ apply (Game8_ipending _ _ _ _ _ b{m} ca{m}).
  + by rewrite get_set_sameE.
  + by rewrite mem_set.
  move => c2 c3.
  rewrite mem_set /=.
  case (inv2 c3) => /#.

case (inv1 a' i').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => b' c1 sma' dm .
  apply (Game8_aborted_i _ _ _ _ _ b' c1) => //.
  + by rewrite get_set_neqE.
  by rewrite mem_set; left.
+ move => b' c1 c2 sma' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ b' c1 c2) => //.
  + by rewrite get_set_neqE.
  by rewrite mem_set; left.
+ move => b' c1 sma' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ b' c1) => //.
  + by rewrite get_set_neqE.
  + by rewrite mem_set; left.
  smt(mem_set).
+ move => b' c1 c2 sma' dmc2.
  apply (Game8_rpending _ _ _ _ _ b' c1 c2) => //.
  + by rewrite get_set_neqE.
  by rewrite mem_set; left.
+ move => b j stb c1 c2 c3 sma' dmc3 nsk smbj c_in_stbj neqbj.
  apply (Game8_accepted_i _ _ _ _ _ b j stb c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  + by rewrite mem_set; left.
  smt(get_set_neqE).
+ move => b' j st c1 c2 c3 sma' dmc3 smbj obs_sk.
  apply (Game8_accepted_r _ _ _ _ _ b' j st c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  + smt(mem_set).
  smt(get_set_neqE).
move => r id1 id2 c1 c2 c3 k sma' dmc3 skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
+ by rewrite get_set_neqE.
by rewrite mem_set; left.

(* Decmap invariant *)
move => c.
case (c = ca{m}) => /> => [| neq].
+ apply (Game8_dm_m1 _ _ _ a{m} b{m} i{m} (IPending (b, witness, witness, ca){m} (a, ca){m})) => //.
  + by rewrite mem_set; right.
  + by rewrite get_set_sameE.
  + move => [b' j'] st'.
    rewrite get_setE.
    case ((b', j') = (a, i){m}) => />.
    move => neq smbj'.
    case (inv1 b' j'); rewrite smbj' //=.
    + smt().
    + smt().
    + move => /> b j stb c1 c2 c3.
      case (inv2 c3); smt().
    move => /> id1 id2 c1 c2 c3.
    by case (inv2 c3); smt().

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  apply (Game8_dm_undef _ _ _) => //.
  + smt(mem_set).
  + smt(mem_set).
  smt(mem_set).

+ move => a' b' i' st dmc smai c_in_st uniq.
  apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).

+ move => a' b' j' st c1 dmc1 dmc smbj c1_in_st c_in_st uniq.
  apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
  + smt(mem_set).
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).

move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai c1_in_st c2_in_st c_in_st uniq.
apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
+ smt(mem_set).
+ smt(mem_set).
+ smt(mem_set).
+ smt(get_setE).
smt(get_setE).

(* Ciphertext Decmap Uniqueness *)
smt(mem_set).

(* Secret Key Decmap *)
smt(mem_set).
qed.

hoare Game8_inv_send_msg2: Game8.send_msg2:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp; if=> //.
sp; match => //.
+ auto=> />.
  move=> &m ? ? inv1 inv2 inv3 inv4 ? ?.
  do! split.

  (* State Map invariant *)
  move=> b' j'.
  case: ((b', j') = (b, j){m}) => /> => [|neq_bj].
  - apply (Game8_aborted_r1 _ _ _ _ _).
    by rewrite get_set_sameE.

  case (inv1 b' j').
  + move => sm.
    apply Game8_undef.
    by rewrite get_set_neqE.
  + move => sm.
    apply (Game8_aborted_r1 _ _ _ _ _).
    by rewrite get_set_neqE.
  + move => a' c1 sma' dm.
    apply (Game8_aborted_i _ _ _ _ _ a' c1) => //.
    by rewrite get_set_neqE.
  + move => a' c1 c2 smb' dmc2.
    apply (Game8_aborted_r2 _ _ _ _ _ a' c1 c2) => //.
    by rewrite get_set_neqE.
  + move => a' c1 smb' dmc1 ndmc1.
    apply (Game8_ipending _ _ _ _ _ a' c1) => //.
    by rewrite get_set_neqE.
  + move => a' c1 c2 smb' dmc2.
    apply (Game8_rpending _ _ _ _ _ a' c1 c2) => //.
    by rewrite get_set_neqE.
  + move => b j stb c1 c2 c3 sma' dmc3 nsk smbj cs_in_stb neqbj.
    apply (Game8_accepted_i _ _ _ _ _ b j stb c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    smt(get_set_neqE).
  + move => a' i st c1 c2 c3 smb' dmc3 smai obs_sk.
    apply (Game8_accepted_r _ _ _ _ _ a' i st c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    smt(get_set_neqE).
  move => r id1 id2 c1 c2 c3 k smb' dmc3 skm_k ids_eq.
  apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
  by rewrite get_set_neqE.

  (* Decmap invariant *)
  move => c.

  case (inv2 c).
  + move => ndm1 ndm2 ndm3.
    exact (Game8_dm_undef _ _ _).

  + move => a' b' i' st dmc smai c_in_st uniq.
    apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
    + smt(get_setE).
    smt(get_setE).

  + move => a' b' j' st c1 dmc1 dmc smbj c1_in_st c_in_st uniq.
    apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
    + smt(get_setE).
    smt(get_setE).

  move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai c1_in_st c2_in_st c_in_st uniq.
  apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
  + smt(get_setE).
  smt(get_setE).

  (* Ciphertext Decmap Uniqueness *)
  exact inv3.

seq 1 : (#pre); 1: by auto.
auto => />.
move => &m ? ? inv1 inv2 inv3 inv4 bj_nin_sm ab_in_psk bad.

do! split.

(* State Map invariant *)
move => b' j'.
case: ((b', j') = (b, j){m}) => /> => [|neq_bj].
- apply (Game8_rpending _ _ _ _ _ a{m} ca{m} cb{m}) => //.
  + by rewrite get_set_sameE.
  by rewrite mem_set; right.

case (inv1 b' j').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => a' c1 sma' dm.
  apply (Game8_aborted_i _ _ _ _ _ a' c1) => //.
  + by rewrite get_set_neqE.
  smt(mem_set).
+ move => a' c1 c2 smb' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ a' c1 c2) => //.
  + by rewrite get_set_neqE.
  smt(mem_set).
+ move => a' c1 smb' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ a' c1) => //.
  + by rewrite get_set_neqE.
  + smt(mem_set).
  smt(mem_set).
+ move => a' c1 c2 smb' dmc2.
  apply (Game8_rpending _ _ _ _ _ a' c1 c2) => //.
  + by rewrite get_set_neqE.
  smt(mem_set).
+ move => b j stb c1 c2 c3 sma' dmc3 nsk smbj cs_in_stb neqbj.
  apply (Game8_accepted_i _ _ _ _ _ b j stb c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  + smt(mem_set).
  smt(get_set_neqE).
+ move => a' i st c1 c2 c3 smb' dmc3 smai obs_sk.
  apply (Game8_accepted_r _ _ _ _ _ a' i st c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  + smt(mem_set).
  smt(get_set_neqE).
move => r id1 id2 c1 c2 c3 k smb' dmc3 skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
+ by rewrite get_set_neqE.
smt(mem_set).

(* Decmap invariant *)
move => c.

case (c = cb{m}) => /> => [| neq].
+ apply (Game8_dm_m2 _ _ _ a{m} b{m} j{m} (RPending (a, witness, witness, witness, ca, cb){m} (a, ca){m} cb{m}) ca{m}) => //.
  + smt(mem_set).
  + by rewrite mem_set.
  + by rewrite get_set_sameE.
  + move => [a' i'] st'.
    rewrite get_setE.
    case ((a', i') = (b, j){m}) => />.
    move => neq smai'.
    case (inv1 a' i'); rewrite smai' //=.
    + smt().
    + smt().
    + move => /> a i st c1 c2 c3.
      case (inv2 c3); smt().
    move => /> id1 id2 c1 c2 c3.
    case (inv2 c3); smt().

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  apply (Game8_dm_undef _ _ _) => //.
  + smt(mem_set).
  + smt(mem_set).
  smt(mem_set).

+ move => a' b' i' st dmc smai c_in_st uniq.
  apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).

+ move => a' b' j' st c1 dmc1 dmc smbj c1_in_st c_in_st uniq.
  apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
  + smt(mem_set).
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).

move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai c1_in_st c2_in_st c_in_st uniq.
apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
+ smt(mem_set).
+ smt(mem_set).
+ smt(mem_set).
+ smt(get_setE).
smt(get_setE).

smt(get_setE).

smt(get_setE).
qed.

hoare Game8_inv_send_msg3: Game8.send_msg3:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp; if=> //.
sp; match => //.
sp; match => //.
+ auto => />.
  move=> &m ? ? inv1 inv2 inv3 inv4 ?.
  have smai : Game8.state_map.[a, i]{m} = Some (role, IPending (b, psk, na, ca) m1){m} by smt().
  case (inv1 a{m} i{m}); rewrite smai //=.
  move => /> !->> dmca ndmca.
  do! split.

  (* State Map invariant *)
  move => a' i'.
  case: ((a', i') = (a, i){m}) => /> => [| neq].
  + apply (Game8_aborted_i _ _ _ _ _ b{m} ca{m}) => //.
    by rewrite get_set_sameE.

  case (inv1 a' i').
  + move => sm.
    apply Game8_undef.
    by rewrite get_set_neqE.
  + move => sm.
    apply (Game8_aborted_r1 _ _ _ _ _).
    by rewrite get_set_neqE.
  + move => b' c1 sma' dm .
    apply (Game8_aborted_i _ _ _ _ _ b' c1) => //.
    by rewrite get_set_neqE.
  + move => b' c1 c2 sma' dmc2.
    apply (Game8_aborted_r2 _ _ _ _ _ b' c1 c2) => //.
    by rewrite get_set_neqE.
  + move => b' c1 sma' dmc1 ndmc1.
    apply (Game8_ipending _ _ _ _ _ b' c1) => //.
    by rewrite get_set_neqE.
  + move => b' c1 c2 sma' dmc2.
    apply (Game8_rpending _ _ _ _ _ b' c1 c2) => //.
    + by rewrite get_set_neqE.
  + move => b' j st c1 c2 c3 sma' dmc3 nsk smbj neq_bj.
    apply (Game8_accepted_i _ _ _ _ _ b' j st c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    smt(get_setE).
  + move => b' j st c1 c2 c3 sma' dmc3 smbj neq_bj.
    apply (Game8_accepted_r _ _ _ _ _ b' j st c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    case ((b', j) = (a, i){m}); 2: smt(get_setE).
    move => />.
    case (inv2 c3); 1..3: smt(get_setE).
    smt(get_set_neqE).
  move => r id1 id2 c1 c2 c3 k sma' dmc3 skm_k ids_eq.
  apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
  by rewrite get_set_neqE.

  (* Decmap invariant *)
  move => c.

  case (inv2 c).
  + move => ndm1 ndm2 ndm3.
    exact (Game8_dm_undef _ _ _).

  + move => a' b' i' st.
    case ((a', i') = (a, i){m}) => /> => [| neq].
    + rewrite smai => /> dmc uniq.
      apply (Game8_dm_m1 _ _ _ a{m} b{m} i{m} (Aborted (I ca{m}))) => //.
      + by rewrite get_set_sameE.
      smt(get_setE).
    move => dmc smai' c_in_st uniq.
    apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
    + smt(get_setE).
    smt(get_setE).

  + move => a' b' j' st c1 dmc1 dmc smbj c1_in_st c_in_st uniq.
    apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
    + smt(get_setE).
    smt(get_setE).

  move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai' c1_in_st c2_in_st c_in_st uniq.
  apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
  + smt(get_setE).
  smt(get_setE).

seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto=> />.
move=> &m bad dm ? inv1 inv2 inv3 inv4 ai_in_sm nbad ? ?.
have smai : Game8.state_map.[a, i]{m} = Some (role, IPending (b, psk, na, ca) m1){m} by smt().
case (inv1 a{m} i{m}); rewrite smai => //.
move => /> !->> ca_in_dm ca3_nin_dm.
have dmm2: (((a, b), msg2_data a b ca, m2) \in Game8.dec_map){m} by smt().
case (inv2 m2{m}); 1,2,4: smt().
move => ? ? j stb c1' _ /(inv3 _ _ _ _ _ dmm2) /> smbj ca_in_stb m2_in_stb uniq.
do! split.

(* State Map invariant *)
move => a' i'.
case: ((a', i') = (a, i){m}) => /> => [| neq].
+ apply (Game8_accepted_i _ _ _ _ _ b{m} j stb ca{m} m2{m} caf{m}) => //.
  + by rewrite get_set_sameE.
  + by rewrite mem_set.
  + smt(get_set_neqE).
  + case (inv1 b{m} j); rewrite smbj //.
    + smt(get_setE).
    + smt(get_setE).
    + move => a'' i'' sta'' c1 c2 c3.
      case (inv2 c3); smt().
    + move =>  /> id1 id2 c1 c2 c3.
      case (inv2 c3); smt().
  smt().

case (inv1 a' i').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => b' c1 sma' dmc1.
  apply (Game8_aborted_i _ _ _ _ _ b' c1) => //.
  + by rewrite get_set_neqE.
  by rewrite mem_set; left.
+ move => b' c1 c2 sma' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ b' c1 c2) => //.
  + by rewrite get_set_neqE.
  by rewrite mem_set; left.
+ move => b' c1 sma' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ b' c1) => //.
  + by rewrite get_set_neqE.
  + by rewrite mem_set; left.
  move => c2 c3.
  case (inv2 ca{m}); smt(mem_set).
+ move => b' c1 c2 sma' dmc2.
  apply (Game8_rpending _ _ _ _ _ b' c1 c2) => //.
  + by rewrite get_set_neqE.
  by rewrite mem_set; left.
+ move => b' j' stb' c1 c2 c3 sma' dmc3 nsk smbj' c_in_stb' neq_bj'.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  smt(get_setE).
+ move => b' j' st c1 c2 c3 sma' dmc3 smbj' obs_sk.
  apply (Game8_accepted_r _ _ _ _ _ b' j' st c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  smt(get_setE).
move => r id1 id2 c1 c2 c3 k sma' dmc3 skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
+ by rewrite get_set_neqE.
by rewrite mem_set; left.

(* Decmap invariant *)
move => c.
case (c = caf{m}) => /> => [| neq].
+ apply (Game8_dm_m3 _ _ _ a{m} b{m} i{m} (Accepted ((a, ca), m2, caf){m} witness) ca{m} m2{m}) => //.
  + smt(mem_set).
  + smt(mem_set).
  + by rewrite mem_set; right.
  + by rewrite get_set_sameE.
  + move => [b' j'] st'.
    rewrite get_setE.
    case ((b', j') = (a, i){m}) => />.
    move => neq smbj'.
    case (inv1 b' j'); rewrite smbj' //=.
    + smt().
    + smt().
    + move => /> b c1 c2 c3.
      case (inv2 c3); smt().
    move => /> id1 id2 c1 c2 c3.
    case (inv2 c3); smt().

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  apply (Game8_dm_undef _ _ _) => //.
  + smt(mem_set).
  + smt(mem_set).
  smt(mem_set).

+ move => a' b' i' st.
  case ((a', i') = (a, i){m}) => /> => [| neq'].
  + rewrite smai => /> dmc uniq'.
    apply (Game8_dm_m1 _ _ _ a{m} b{m} i{m} (Accepted ((a, ca), m2, caf){m} witness)) => //.
    + smt(mem_set).
    + by rewrite get_set_sameE.
    smt(get_setE).
  move => dmc smai' c_in_st uniq'.
  apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).

+ move => a' b' j' st c1 dmc1 dmc smbj' c1_in_st c_in_st uniq'.
  apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
  + smt(mem_set).
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).

move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai' c1_in_st c2_in_st c_in_st uniq'.
apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
+ smt(mem_set).
+ smt(mem_set).
+ smt(mem_set).
+ smt(get_setE).
case (inv2 ca{m}); smt(get_setE).

(* Ciphertext Decmap Uniqueness *)
smt(mem_set).

smt(mem_set).
qed.

hoare Game8_inv_send_fin: Game8.send_fin:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  move=> &m ? ? inv1 inv2 inv3 inv4 ?.
  have smbj : Game8.state_map.[b, j]{m} = Some (role, RPending (a, psk, na, nb, ca, cb) m1 m2){m} by smt().
  case (inv1 b{m} j{m}); rewrite smbj //=.
  move => /> !->> dmcb.
  do! split.

  (* State Map invariant *)
  move=> b' j'.
  case: ((b', j') = (b, j){m}) => /> => [|neq_bj].
  - apply (Game8_aborted_r2 _ _ _ _ _ a{m} ca{m} cb{m}) => //.
    by rewrite get_set_sameE.

  case (inv1 b' j').
  + move => sm.
    apply Game8_undef.
    by rewrite get_set_neqE.
  + move => sm.
    apply (Game8_aborted_r1 _ _ _ _ _).
    by rewrite get_set_neqE.
  + move => a' c1 sma' dm.
    apply (Game8_aborted_i _ _ _ _ _ a' c1) => //.
    by rewrite get_set_neqE.
  + move => a' c1 c2 smb' dmc2.
    apply (Game8_aborted_r2 _ _ _ _ _ a' c1 c2) => //.
    by rewrite get_set_neqE.
  + move => a' c1 smb' dmc1 ndmc1.
    apply (Game8_ipending _ _ _ _ _ a' c1) => //.
    by rewrite get_set_neqE.
  + move => a' c1 c2 smb' dmc2.
    apply (Game8_rpending _ _ _ _ _ a' c1 c2) => //.
    by rewrite get_set_neqE.
  + move => a' i st c1 c2 c3.
    case ((a', i) = (b, j){m}).
    + move => />.
      rewrite smbj => /> smbj' dmc3 nsk ? ? ?.
      apply (Game8_accepted_i _ _ _ _ _ b{m} j{m} (Aborted (R2 ca{m} cb{m})) c1 c2 c3) => //.
      + by rewrite get_set_neqE.
      smt(get_setE).
    move => neq smbj' dmc3 nsk smai' c_in_st neq_ai.
    apply (Game8_accepted_i _ _ _ _ _ a' i st c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    smt(get_setE).
  + move => a' i st c1 c2 c3 smb' dmc3 smai obs_sk.
    apply (Game8_accepted_r _ _ _ _ _ a' i st c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    smt(get_set_neqE).
  move => r id1 id2 c1 c2 c3 k smb' dmc3 skm_k ids_eq.
  apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
  by rewrite get_set_neqE.

  (* Decmap invariant *)
  move => c.

  case (inv2 c).
  + move => ndm1 ndm2 ndm3.
    exact (Game8_dm_undef _ _ _).

  + move => a' b' i' st dmc smai c_in_st uniq.
    apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
    + smt(get_setE).
    smt(get_setE).

  + move => a' b' j' st c1.
    case ((b', j') = (b, j){m}) => /> => [| neq].
    + rewrite smbj => /> dmc1 dmc c1_eqs c_eqs uniq.
      apply (Game8_dm_m2 _ _ _ a{m} b{m} j{m} (Aborted (R2 ca{m} cb{m})) ca{m}) => //.
      + smt().
      + smt().
      + by rewrite get_set_sameE.
      smt(get_setE).
    move => dmc1 dmc smbj' c1_in_st c_in_st uniq.
    apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
    + smt(get_setE).
    smt(get_setE).

  move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai c1_in_st c2_in_st c_in_st uniq.
  apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
  + smt(get_setE).
  smt(get_setE).

auto=> />.
move=> &m ? ? inv1 inv2 inv3 inv4 bjin.
have smbj : Game8.state_map.[b, j]{m} = Some (role, RPending (a, psk, na, nb, ca, cb) m1 m2){m} by smt().
case (inv1 b{m} j{m}); rewrite smbj //=.
move => /> !->> dmcb.
have dmm3: (((a, b), msg3_data a b ca cb, m3) \in Game8.dec_map){m} by smt().
case (inv2 m3{m}); 1..3: smt().
move => a' b' i sta c1 c2 dmca _ /(inv3 _ _ _ _ _ dmm3) /> smai ca_in_sta cb_in_sta m3_in_sta uniq.
clear a' b' c1 c2.
do! split.

(* State Map invariant *)
move=> b' j'.
case: ((b', j') = (b, j){m}) => /> => [|neq_bj].
- apply (Game8_accepted_r _ _ _ _ _ a{m} i sta ca{m} cb{m} m3{m}) => //.
  + smt(get_setE).
  + smt(get_setE).
  + by case: (inv1 a{m} i); rewrite smai=> // /#.
  + case (inv1 a{m} i); rewrite smai=> // />.
    + smt().
    + smt().
    by case (inv2 cb{m})=> /#.

case (inv1 b' j').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => a' c1 sma' dm.
  apply (Game8_aborted_i _ _ _ _ _ a' c1) => //.
  by rewrite get_set_neqE.
+ move => a' c1 c2 smb' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ a' c1 c2) => //.
  by rewrite get_set_neqE.
+ move => a' c1 smb' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ a' c1) => //.
  by rewrite get_set_neqE.
+ move => a' c1 c2 smb' dmc2.
  apply (Game8_rpending _ _ _ _ _ a' c1 c2) => //.
  by rewrite get_set_neqE.
+ move => b'' j'' st c1 c2 c3.
  case ((b'', j'') = (b, j){m}).
  + move => />.
    rewrite smbj => /> smbj' dmc3 nsk ? ? ?.
    apply (Game8_accepted_i _ _ _ _ _ b{m} j{m} (Accepted ((a, ca), cb, m3) witness){m} c1 c2 c3) => //.
    + by rewrite get_set_neqE.
    + by rewrite get_set_sameE.
    + smt().
    case (inv2 ca{m}); 1,3,4: smt().
    move => a'' b''' i' sta'' /(inv3 _ _ _ _ _ dmca) [] [] /= <*> /=.
    move => _ _ uniq'.
    clear sta''.
    case (inv2 c3) => /#.
  move => neq sma' dmc3 nsk smai' c_in_st neq'.
  apply (Game8_accepted_i _ _ _ _ _ b'' j'' st c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  smt(get_set_neqE).
+ move => a' i' st c1 c2 c3 smb' dmc3 smai' obs_sk.
  apply (Game8_accepted_r _ _ _ _ _ a' i' st c1 c2 c3) => //.
  + by rewrite get_set_neqE.
  smt(get_set_neqE).
move => r id1 id2 c1 c2 c3 k smb' dmc3 skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1 c2 c3 k) => //.
by rewrite get_set_neqE.

(* Decmap invariant *)
move => c.

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  exact (Game8_dm_undef _ _ _).

+ move => a' b' i' st dmc smai' c_in_st uniq'.
  apply (Game8_dm_m1 _ _ _ a' b' i' st) => //.
  + smt(get_setE).
  smt(get_setE).

+ move => a' b' j' st c1.
  case ((b', j') = (b, j){m}) => /> => [| neq].
  + rewrite smbj => /> dmc1 dmc c1_eqs c_eqs uniq'.
    apply (Game8_dm_m2 _ _ _ a{m} b{m} j{m} (Accepted ((a, ca), cb, m3){m} witness) ca{m}) => //.
    + smt().
    + by rewrite get_set_sameE.
    smt(get_setE).
    smt(get_setE).
  move => dmc1 dmc smbj' c1_in_st c_in_st uniq'.
  apply (Game8_dm_m2 _ _ _ a' b' j' st c1) => //.
  + smt(get_setE).
  smt(get_setE).

move => a' b' i' st c1 c2 dmc1 dmc2 dmc smai' c1_in_st c2_in_st c_in_st uniq'.
apply (Game8_dm_m3 _ _ _ a' b' i' st c1 c2) => //.
+ smt(get_setE).
smt(get_setE).
qed.

hoare Game8_inv_reveal: Game8.reveal:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
rcondt ^if.
+ auto => /> &m st inv1 inv2 inv3 inv4 aiin card_obs_ps sk _.
  have smai : Game8.state_map.[a, i]{m} = Some (role{m}, Accepted trace{m} k'{m}) by smt().
  case (inv1 a{m} i{m}); rewrite smai //.
  + move => />.
    move => b j stb c1 c2 c3 !->> dmc3 smbj.
    case (inv1 b j); rewrite smbj //.
    move => />.
    move => id1 id2 c1' c2' c3' k'.
    move => ->>.
    case (inv2 c3'); 1..3: smt().
    case (c1' = c1); 2: smt().
    case (c2' = c2); 2: smt().
    case (c3' = c3); 2: smt().
    case (id1 = a{m}); 2: smt().
    move => />.
    have bj_partner : (b, j) \in get_partners (Some ((a{m}, c1), c2, c3)) Initiator Game8.state_map{m}.
    + rewrite /get_partners mem_fdom mem_filter /#.
    have // : (b, j) \in get_observed_partners (a, i){m} Game8.state_map{m}.
    + rewrite /get_observed_partners in_filter /#.
    rewrite fcard_eq0 in card_obs_ps.
    by rewrite card_obs_ps in_fset0.
  move => />.
  move => b j stb c1 c2 c3 !->> dmc3 smbj.
  case (inv1 b j); rewrite smbj //.
  move => />.
  move => id1 id2 c1' c2' c3' k'.
  move => ->>.
  case (inv2 c3'); 1..3: smt().
  case (c1' = c1); 2: smt().
  case (c2' = c2); 2: smt().
  case (c3' = c3); 2: smt().
  case (id1 = b); 2: smt().
  move => />.
  have bj_partner : (b, j) \in get_partners (Some ((b, c1), c2, c3)) Responder Game8.state_map{m}.
  + rewrite /get_partners mem_fdom mem_filter /#.
  have // : (b, j) \in get_observed_partners (a, i){m} Game8.state_map{m}.
  + rewrite /get_observed_partners in_filter /#.
  rewrite fcard_eq0 in card_obs_ps.
  by rewrite card_obs_ps in_fset0.

auto => /> &m st inv1 inv2 inv3 inv4 aiin card_obs_ps sk _.
rewrite get_set_sameE //=.

case: (role{m}) aiin st => /> /domE; case _: (Game8.state_map.[a, i]{m})=> /> smai.
case (inv1 a{m} i{m}); rewrite smai=> //=.
move => /> b j stb c1 c2 c3 !->> dmc3 smbj c1_in_stb c2_in_stb c3_in_stb nskm.
do! split.

(* State Map invariant *)
move=> a' i'.
case: ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game8_observed _ _ _ _ _ Initiator a{m} b c1 c2 c3 sk) => //.
  + by rewrite get_set_sameE.
  by rewrite mem_set; right.

case (inv1 a' i').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => b' c1' smb' dm.
  apply (Game8_aborted_i _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' c1' sma' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_rpending _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' j' stb' c1' c2' c3' sma' dmc3' smbj' c_in_stb' c3'_tr obs_sk.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  + case (inv2 c3); smt(get_setE).
+ move => b'' j' stb' c1' c2' c3'.
  case ((b'', j') = (a, i){m}).
  + move => />.
    rewrite smai => /> smai' dmc3'.
    case (inv2 c3'); 1..3: smt().
    move => />.
    have /> := inv3 _ _ _ _ _ dmc3 dmc3'.
    move => *.
    apply (Game8_accepted_r _ _ _ _ _ a{m} i{m} (Observed ((a{m}, c1'), c2', c3') sk) c1' c2' c3') => //.
    + smt(get_setE).
    by rewrite get_set_sameE.
  move => neqbj' sma' dmc3' smbj' c_in_stb obs_skmn.
  apply (Game8_accepted_r _ _ _ _ _ b'' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  by case (inv2 c3); smt(get_setE).
move => r id1 id2 c1' c2' c3' k smb' dmc3' skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1' c2' c3' k) => //.
+ by rewrite get_set_neqE.
+ rewrite mem_set; left.
exact skm_k.

(* Decmap invariant *)
move => c.

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  exact (Game8_dm_undef _ _ _).

+ move => a' b' i'.
  case ((a', i') = (a, i){m}) => />.
  + rewrite smai => />.
    move => dmc eq_c uniq.
    apply (Game8_dm_m1 _ _ _ a{m} b' i{m} (Observed ((a{m}, c1), c2, c3) sk)) => //.
    + by rewrite get_set_sameE.
    smt(get_setE).
  move => neq st' dmc smai' c_in_st uniq.
  apply (Game8_dm_m1 _ _ _ a' b' i' st') => //.
  + by rewrite get_set_neqE.
  smt(get_setE).

+ move => a' b' j' st' c1' dmc1' dmc smbj' c1_in_st c_in_st uniq.
  apply (Game8_dm_m2 _ _ _ a' b' j' st' c1') => //.
  + smt(get_setE).
  smt(get_setE).

move => a' b' i'.
case ((a', i') = (a, i){m}) => />.
+ rewrite smai => />.
  move => c1' c2' dmc1' dmc2' dmc smai' c1_in_st c2_in_st uniq.
  apply (Game8_dm_m3 _ _ _ a{m} b' i{m} (Observed ((a{m}, c1), c2, c3) sk) c1 c2) => //.
  + smt(mem_set).
  + smt(mem_set).
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).
move => neq st' c1' c2' dmc1' dmc2' dmc smai' c1_in_st c2_in_st c_in_st uniq.
apply (Game8_dm_m3 _ _ _ a' b' i' st' c1' c2') => //.
+ smt(get_setE).
smt(get_setE).

smt(get_setE).

case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stbj c1 c2 c3 !->> dmc3 smbj trace_stbj obs_skm.
do! split.

(* State Map invariant *)
move=> a' i'.
case: ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game8_observed _ _ _ _ _ Responder b a{m} c1 c2 c3 sk) => //.
  + by rewrite get_set_sameE.
  by rewrite mem_set; right.

case (inv1 a' i').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => b' c1' smb' dm.
  apply (Game8_aborted_i _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' c1' sma' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_rpending _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' j' stb' c1' c2' c3'.
  case ((b', j') = (a, i){m}).
  + move => />.
    rewrite smai => /> *.
    apply (Game8_accepted_i _ _ _ _ _ a{m} i{m} (Observed ((b, c1), c2, c3) sk) c1' c2' c3') => //.
    + by rewrite get_set_neqE.
    + by rewrite get_set_sameE.
  move => neq' smai' dmc3' smbj' c_in_stb' c3'_tr obs_sk.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  move => ^ /obs_sk.
  rewrite mem_set negb_or //=.
  case (c3' = c3); 2: smt().
  case (c2' = c2); 2: smt().
  case (c1' = c1); 2: smt().
  move => />.
  case (inv2 c3); 1..3: smt().
  case (inv2 c2); 1,2,4: smt().
  smt().
+ move => b' j' stb c1' c2' c3' sma' dmc3' smbj' c_in_stb obs_sk.
  apply (Game8_accepted_r _ _ _ _ _ b' j' stb c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  case (inv2 c3); 1..3: smt().
  case (inv2 c2); 1,2,4: smt().
  smt(mem_set).
move => r id1 id2 c1' c2' c3' k smb' dmc3' skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1' c2' c3' k) => //.
+ by rewrite get_set_neqE.
+ rewrite mem_set; left.
exact skm_k.

(* Decmap invariant *)
move => c.

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  exact (Game8_dm_undef _ _ _).

+ move => a' b' i' st' dmc smai' c_in_st' uniq.
  apply (Game8_dm_m1 _ _ _ a' b' i' st') => //.
  + smt(get_setE).
  smt(get_setE).

+ move => a' b' j' st' c1'.
  case ((b', j') = (a, i){m}).
  + move => /> *.
    apply (Game8_dm_m2 _ _ _ a' a{m} i{m} (Observed ((b, c1), c2, c3) sk) c1') => //.
    + smt(get_setE).
    + smt(get_setE).
    + smt(get_setE).
    smt(get_setE).
  move => neq' dmc1' dmc smbj' c1_in_st c_in_st uniq.
  apply (Game8_dm_m2 _ _ _ a' b' j' st' c1') => //.
  + smt(get_setE).
  smt(get_setE).

move => a' b' i'.
move => st' c1' c2' dmc1' dmc2' dmc smai' c1_in_st c2_in_st c_in_st uniq.
apply (Game8_dm_m3 _ _ _ a' b' i' st' c1' c2') => //.
+ smt(get_setE).
smt(get_setE).

smt(get_setE).
qed.

hoare Game8_inv_test: Game8.test:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
rcondt ^if.
+ auto => /> &m st inv1 inv2 inv3 inv4 aiin card_obs_ps sk _.
  have smai : Game8.state_map.[a, i]{m} = Some (role{m}, Accepted trace{m} k'{m}) by smt().
  case (inv1 a{m} i{m}); rewrite smai //.
  + move => />.
    move => b j stb c1 c2 c3 !->> dmc3 smbj.
    case (inv1 b j); rewrite smbj //.
    move => />.
    move => id1 id2 c1' c2' c3' k'.
    move => ->>.
    case (inv2 c3'); 1..3: smt().
    case (c1' = c1); 2: smt().
    case (c2' = c2); 2: smt().
    case (c3' = c3); 2: smt().
    case (id1 = a{m}); 2: smt().
    move => />.
    have bj_partner : (b, j) \in get_partners (Some ((a{m}, c1), c2, c3)) Initiator Game8.state_map{m}.
    + rewrite /get_partners mem_fdom mem_filter /#.
    have // : (b, j) \in get_observed_partners (a, i){m} Game8.state_map{m}.
    + rewrite /get_observed_partners in_filter /#.
    rewrite fcard_eq0 in card_obs_ps.
    by rewrite card_obs_ps in_fset0.
  move => />.
  move => b j stb c1 c2 c3 !->> dmc3 smbj.
  case (inv1 b j); rewrite smbj //.
  move => />.
  move => id1 id2 c1' c2' c3' k'.
  move => ->>.
  case (inv2 c3'); 1..3: smt().
  case (c1' = c1); 2: smt().
  case (c2' = c2); 2: smt().
  case (c3' = c3); 2: smt().
  case (id1 = b); 2: smt().
  move => />.
  have bj_partner : (b, j) \in get_partners (Some ((b, c1), c2, c3)) Responder Game8.state_map{m}.
  + rewrite /get_partners mem_fdom mem_filter /#.
  have // : (b, j) \in get_observed_partners (a, i){m} Game8.state_map{m}.
  + rewrite /get_observed_partners in_filter /#.
  rewrite fcard_eq0 in card_obs_ps.
  by rewrite card_obs_ps in_fset0.

seq 1 : #pre; 1: by auto => />.
sp.
seq 1 : #pre; 1: by auto => />.

auto => /> &m skm st inv1 inv2 inv3 inv4 aiin card_obs_ps.

case: (role{m}) aiin st => /> /domE; case _: (Game8.state_map.[a, i]{m})=> /> smai.
case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stb c1 c2 c3 !->> dmc3 smbj c1_in_stb c2_in_stb c3_in_stb nskm.
do! split.

(* State Map invariant *)
move=> a' i'.
case: ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game8_observed _ _ _ _ _ Initiator a{m} b c1 c2 c3 k{m}) => //.
  + by rewrite get_set_sameE.
  by rewrite mem_set; right.

case (inv1 a' i').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => b' c1' smb' dm.
  apply (Game8_aborted_i _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' c1' sma' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_rpending _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' j' stb' c1' c2' c3' sma' dmc3' smbj' c_in_stb' c3'_tr obs_sk.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  + by case (inv2 c3'); smt(get_setE).
+ move => b'' j' stb' c1' c2' c3'.
  case ((b'', j') = (a, i){m}).
  + move => />.
    rewrite smai => /> smai' dmc3'.
    case (inv2 c3'); 1..3: smt(get_setE).
    move => />.
    have /> := inv3 _ _ _ _ _ dmc3 dmc3'.
    move => *.
    apply (Game8_accepted_r _ _ _ _ _ a{m} i{m} (Observed ((a{m}, c1'), c2', c3') k{m}) c1' c2' c3') => //.
    + smt(get_setE).
    by rewrite get_set_sameE.
  move => neqbj' sma' dmc3' smbj' c_in_stb obs_skmn.
  apply (Game8_accepted_r _ _ _ _ _ b'' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  by case (inv2 c3'); smt(get_setE).
move => r id1 id2 c1' c2' c3' k smb' dmc3' skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1' c2' c3' k) => //.
+ by rewrite get_set_neqE.
+ rewrite mem_set; left.
exact skm_k.

(* Decmap invariant *)
move => c.

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  exact (Game8_dm_undef _ _ _).

+ move => a' b' i'.
  case ((a', i') = (a, i){m}) => />.
  + rewrite smai => />.
    move => dmc eq_c uniq.
    apply (Game8_dm_m1 _ _ _ a{m} b' i{m} (Observed ((a{m}, c1), c2, c3) k{m})) => //.
    + by rewrite get_set_sameE.
    smt(get_setE).
  move => neq st' dmc smai' c_in_st uniq.
  apply (Game8_dm_m1 _ _ _ a' b' i' st') => //.
  + by rewrite get_set_neqE.
  smt(get_setE).

+ move => a' b' j' st' c1' dmc1' dmc smbj' c1_in_st c_in_st uniq.
  apply (Game8_dm_m2 _ _ _ a' b' j' st' c1') => //.
  + smt(get_setE).
  smt(get_setE).

move => a' b' i'.
case ((a', i') = (a, i){m}) => />.
+ rewrite smai => />.
  move => c1' c2' dmc1' dmc2' dmc smai' c1_in_st c2_in_st uniq.
  apply (Game8_dm_m3 _ _ _ a{m} b' i{m} (Observed ((a{m}, c1), c2, c3) k{m}) c1 c2) => //.
  + smt(mem_set).
  + smt(mem_set).
  + smt(mem_set).
  + smt(get_setE).
  smt(get_setE).
move => neq st' c1' c2' dmc1' dmc2' dmc smai' c1_in_st c2_in_st c_in_st uniq.
apply (Game8_dm_m3 _ _ _ a' b' i' st' c1' c2') => //.
+ smt(get_setE).
smt(get_setE).

smt(get_setE).

case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stbj c1 c2 c3 !->> dmc3 smbj trace_stbj obs_skm.
do! split.

(* State Map invariant *)
move=> a' i'.
case: ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game8_observed _ _ _ _ _ Responder b a{m} c1 c2 c3 k{m}) => //.
  + by rewrite get_set_sameE.
  by rewrite mem_set; right.

case (inv1 a' i').
+ move => sm.
  apply Game8_undef.
  by rewrite get_set_neqE.
+ move => sm.
  apply (Game8_aborted_r1 _ _ _ _ _).
  by rewrite get_set_neqE.
+ move => b' c1' smb' dm.
  apply (Game8_aborted_i _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_aborted_r2 _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' c1' sma' dmc1 ndmc1.
  apply (Game8_ipending _ _ _ _ _ b' c1') => //.
  by rewrite get_set_neqE.
+ move => b' c1' c2' sma' dmc2.
  apply (Game8_rpending _ _ _ _ _ b' c1' c2') => //.
  by rewrite get_set_neqE.
+ move => b' j' stb' c1' c2' c3'.
  case ((b', j') = (a, i){m}).
  + move => />.
    rewrite smai => /> *.
    apply (Game8_accepted_i _ _ _ _ _ a{m} i{m} (Observed ((b, c1), c2, c3) k{m}) c1' c2' c3') => //.
    + by rewrite get_set_neqE.
    + by rewrite get_set_sameE.
  move => neq' smai' dmc3' smbj' c_in_stb' c3'_tr obs_sk.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  move => ^ /obs_sk.
  rewrite mem_set negb_or //=.
  case (c3' = c3); 2: smt().
  case (c2' = c2); 2: smt().
  case (c1' = c1); 2: smt().
  move => />.
  case (inv2 c3); 1..3: smt().
  case (inv2 c2); 1,2,4: smt().
  smt().
+ move => b' j' stb c1' c2' c3' sma' dmc3' smbj' c_in_stb obs_sk.
  apply (Game8_accepted_r _ _ _ _ _ b' j' stb c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  case (inv2 c3); 1..3: smt().
  case (inv2 c2); 1,2,4: smt().
  smt(mem_set).
move => r id1 id2 c1' c2' c3' k smb' dmc3' skm_k ids_eq.
apply (Game8_observed _ _ _ _ _ r id1 id2 c1' c2' c3' k) => //.
+ by rewrite get_set_neqE.
+ rewrite mem_set; left.
exact skm_k.

(* Decmap invariant *)
move => c.

case (inv2 c).
+ move => ndm1 ndm2 ndm3.
  exact (Game8_dm_undef _ _ _).

+ move => a' b' i' st' dmc smai' c_in_st' uniq.
  apply (Game8_dm_m1 _ _ _ a' b' i' st') => //.
  + smt(get_setE).
  smt(get_setE).

+ move => a' b' j' st' c1'.
  case ((b', j') = (a, i){m}).
  + move => /> *.
    apply (Game8_dm_m2 _ _ _ a' a{m} i{m} (Observed ((b, c1), c2, c3) k{m}) c1') => //.
    + smt(get_setE).
    + smt(get_setE).
    + smt(get_setE).
    smt(get_setE).
  move => neq' dmc1' dmc smbj' c1_in_st c_in_st uniq.
  apply (Game8_dm_m2 _ _ _ a' b' j' st' c1') => //.
  + smt(get_setE).
  smt(get_setE).

move => a' b' i'.
move => st' c1' c2' dmc1' dmc2' dmc smai' c1_in_st c2_in_st c_in_st uniq.
apply (Game8_dm_m3 _ _ _ a' b' i' st' c1' c2') => //.
+ smt(get_setE).
smt(get_setE).

smt(get_setE).
qed.
