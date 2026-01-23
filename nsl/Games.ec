require import AllCore FMap FSet Distr NSL List.
import GAKEc AEADc.

(* ------------------------------------------------------------------------------------------ *)
(* Intermediate Games *)
(* ------------------------------------------------------------------------------------------ *)

(* Inlining real game with protocol *)
module Game1 = {
  var b0 : bool
  var state_map: (id * int, role * session_state) fmap
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
      ca <$ enc (oget psk_map.[a, b]) (msg1_data a b) na;
      state_map.[a, i] <- (Initiator, IPending (b, (oget psk_map.[a, b]), na, ca) (a, ca));
      mo <- Some ca;
    }
    return mo;
  }

  proc send_msg2(b, j, m1) = {
    var a, ca, nb, cb;
    var mo <- None;

    (a, ca) <- m1;
    if ((b, j) \notin state_map /\ (a, b) \in psk_map) {
      if (dec (oget psk_map.[a, b]) (msg1_data a b) ca is Some na) {
        nb <$ dnonce;
        cb <$ enc (oget psk_map.[a, b]) (msg2_data a b ca) nb;
        state_map.[b, j] <- (Responder, RPending (a, (oget psk_map.[a, b]), na, nb, ca, cb) m1 cb);
        mo <- Some cb;
      } else {
        state_map.[b, j] <- (Responder, Aborted);
      }
    }
    return mo;
  }

  proc send_msg3(a, i, m2) = {
    var r, s, b, psk, na, ca, nok, cok, k;
    var mo <- None;

    if ((a, i) \in state_map) {
      (r, s) <- oget state_map.[a, i];
      if (s is IPending si m1) {
        (b, psk, na, ca) <- si;
        if (dec psk (msg2_data a b ca) m2 is Some nb) {
          nok <$ dnonce;
          cok <$ enc psk (msg3_data a b ca m2) nok;
          k <- prf (na, nb) (a, b);
          state_map.[a, i] <- (Initiator, Accepted (m1, m2, cok) k);
          mo <- Some cok;
         } else {
          state_map.[a, i] <- (Initiator, Aborted);
        }
      }
    }
    return mo;
  }

  proc send_fin(b, j, m3) = {
    var r, s, a, psk, na, nb, ca, cb, k;
    var mo <- None;

    if ((b, j) \in state_map) {
      (r, s) <- oget state_map.[b, j];
      if (s is RPending sr m1 m2) {
        (a, psk, na, nb, ca, cb) <- sr;
        if (dec psk (msg3_data a b ca cb) m3 is Some nok) {
          k <- prf (na, nb) (a, b);
          state_map.[b, j] <- (Responder, Accepted (m1, m2, m3) k);
          mo <- Some ();
        } else {
          state_map.[b, j] <- (Responder, Aborted);
        }
      }
    }
    return mo;
  }

  proc reveal(h) = {
    var r, s;
    var ko <- None;

    if (h \in state_map) {
      (r, s) <- oget state_map.[h];
      match s with
      | Accepted t k => {
        if (fresh h state_map) {
          state_map.[h] <- (r, Observed t k);
          ko <- Some k;
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

  proc test(h) = {
    var r, s, k';
    var ko <- None;

    if (h \in state_map) {
      (r, s) <- oget state_map.[h];
      match s with
      | Accepted t k => {
        if (fresh h state_map) {
          if (b0 = false) {
            k' <- k;
          } else {
            k' <$ dskey;
          }
          state_map.[h] <- (r, Observed t k');
          ko <- Some k';
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

(* Cleanup session state: no longer store key, and ciphertexts (or partner id on responder side). *)
module Game1a = Game1 with {
  proc send_msg1 [
    ^if.^state_map<- ~ { state_map.[a, i] <- (Initiator, IPending (b, witness, na, witness) (a, ca)); }
  ]
  proc send_msg2 [
    ^if.^match#Some.^state_map<- ~ { state_map.[b, j] <- (Responder, RPending (witness, witness, na, nb, witness, witness) m1 cb); }
  ]
  proc send_msg3 [
    ^if.^match#IPending.^match ~ (dec (oget psk_map.[m1.`1, b]) (msg2_data m1.`1 b m1.`2) m2)
    [^if.^match#IPending.^match#Some.^cok<$ - ^k<-] ~ {
      cok <$ enc (oget psk_map.[m1.`1, b]) (msg3_data m1.`1 b m1.`2 m2) nok;
      k <- prf (na, nb) (m1.`1, b);
    }
  ]
  proc send_fin [
    ^if.^match#RPending.^match ~ (dec (oget psk_map.[m1.`1, b]) (msg3_data m1.`1 b m1.`2 m2) m3)
    ^if.^match#RPending.^match#Some.^k<- ~ { k <- prf (na, nb) (m1.`1, b); }
  ]
}.

(* Decmap instead of real enc/dec *)
module Game2 = Game1a with {
  var dec_map: (msg_data * ctxt, nonce) fmap
  var bad : bool

  proc init_mem [
    -1 + { dec_map <- empty; bad <- false; }
  ]
  proc send_msg1 [
    [^if.^na<$ - ^ca<$] ~ {
      ca <$ dctxt;
      bad <- bad \/ exists ad, (ad, ca) \in dec_map;
      na <$ dnonce;
      dec_map.[msg1_data a b, ca] <- na;
     }
  ]
  proc send_msg2 [
    ^if.^match ~ (dec_map.[msg1_data a b, ca])
    [^if.^match#Some.^nb<$ - ^cb<$] ~ {
      cb <$ dctxt;
      bad <- bad \/ exists ad, (ad, cb) \in dec_map;
      nb <$ dnonce;
      dec_map.[msg2_data a b ca, cb] <- nb;
     }
  ]
  proc send_msg3 [
    ^if.^match#IPending.^match ~ (dec_map.[msg2_data m1.`1 b m1.`2, m2])
    [^if.^match#IPending.^match#Some.^nok<$ - ^cok<$] ~ {
      cok <$ dctxt;
      bad <- bad \/ exists ad, (ad, cok) \in dec_map;
      nok <$ dnonce;
      dec_map.[msg3_data m1.`1 b m1.`2 m2, cok] <- nok;
     }
  ]
  proc send_fin [
    ^if.^match#RPending.^match ~ (dec_map.[msg3_data m1.`1 b m1.`2 m2, m3])
  ]
}.

(* No ctxt collisions *)
module Game3 = Game2 with {
  proc send_msg1 [[^if.^bad<- - ^mo<-] + (!bad)]
  proc send_msg2 [[^if.^match#Some.^bad<- - ^mo<-] + (!bad)]
  proc send_msg3 [[^if.^match#IPending.^match#Some.^bad<- - ^mo<-] + (!bad)]
}.

(* Cleanup session state: no longer store nonces *)
module Game3a = Game3 with {
  proc send_msg1 [
    ^if.^if.^state_map<- ~ {
      state_map.[a, i] <- (Initiator, IPending (b, witness, witness, witness) (a, ca));
    }
  ]
  proc send_msg2 [
    ^if.^match#Some.^if.^state_map<- ~ {
      state_map.[b, j] <- (Responder, RPending (witness, witness, witness, witness, witness, witness) m1 cb);
    }
  ]
  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^k<- ~ {
      k <- prf (oget (dec_map.[msg1_data m1.`1 b, m1.`2]), nb) (m1.`1, b);
    }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^k<- ~ {
      k <- prf (oget (dec_map.[msg1_data m1.`1 b, m1.`2]), oget (dec_map.[msg2_data m1.`1 b m1.`2, m2])) (m1.`1, b);
    }
  ]
}.

(* Simply log decryptions use explicit nonce storage *)
module Game3b = Game3a with {
  var nonce_map : (msg_data * ctxt, nonce) fmap

  proc init_mem [-1 + { nonce_map <- empty; }]
  proc send_msg1 [
    ^if.^if.^dec_map<- ~ {
      nonce_map.[msg1_data a b, ca] <- na;
      dec_map.[msg1_data a b, ca] <- witness;
    }
  ]
  proc send_msg2 [
    ^if.^match#Some.^if.^dec_map<- ~ {
      nonce_map.[msg2_data a b ca, cb] <- nb;
      dec_map.[msg2_data a b ca, cb] <- witness;
    }
  ]
  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^dec_map<- ~ {
      dec_map.[msg3_data m1.`1 b m1.`2 m2, cok] <- witness;
    }
    ^if.^match#IPending.^match#Some.^if.^k<- ~ {
      k <- prf (oget nonce_map.[msg1_data m1.`1 b, m1.`2], oget nonce_map.[msg2_data m1.`1 b m1.`2, m2]) (m1.`1, b);
    }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^k<- ~ {
      k <- prf (oget nonce_map.[msg1_data m1.`1 b, m1.`2], oget nonce_map.[msg2_data m1.`1 b m1.`2, m2]) (m1.`1, b);
    }
  ]
}.

(* Delay sampling of nonces until use *)
module Game3c = Game3b with {
  proc send_msg1 [
    ^if.^if.^na<$ -
    ^if.^if.^nonce_map<- -
  ]
  proc send_msg2 [
    ^if.^match#Some.^if.^nb<$ -
    ^if.^match#Some.^if.^nonce_map<- -
  ]
  proc send_msg3 [
    var nb' : nonce
    ^if.^match#IPending.^match#Some.^if.^k<- + ^ {
      na <$ dnonce;
      nb' <$ dnonce;
      if ((msg1_data m1.`1 b, m1.`2) \notin nonce_map) {
        nonce_map.[msg1_data m1.`1 b, m1.`2] <- na;
      }
      if ((msg2_data m1.`1 b m1.`2, m2) \notin nonce_map) {
        nonce_map.[msg2_data m1.`1 b m1.`2, m2] <- nb';
      }
    }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^k<- + ^ {
      na <$ dnonce;
      nb <$ dnonce;
      if ((msg1_data m1.`1 b, m1.`2) \notin nonce_map) {
        nonce_map.[msg1_data m1.`1 b, m1.`2] <- na;
      }
      if ((msg2_data m1.`1 b m1.`2, m2) \notin nonce_map) {
        nonce_map.[msg2_data m1.`1 b m1.`2, m2] <- nb;
      }
    }
  ]
}.

(* Remove guards for retrieving nonces *)
module Game3d = Game3c with {
  proc send_msg3 [^if.^match#IPending.^match#Some.^if.^if - .^if.^match#IPending.^match#Some.^if.^if - .]
  proc send_fin [[^if.^match#RPending.^match#Some.^na<$ - ^if{2}] -]
}.

(* Merge nonce_map into one *)
module Game4 = Game3d with {
  - var nonce_map
  var prfkey_map : (msg_data * ctxt, nonce * nonce) fmap

  proc init_mem [ ^bad<- & +1
                 -1 + { prfkey_map <- empty; }]
  proc send_msg3 [
    [^if.^match#IPending.^match#Some.^if.^<-{2} - ^k<-] ~ {
      prfkey_map.[msg3_data m1.`1 b m1.`2 m2, cok] <- (na, nb');
      k <- prf (oget prfkey_map.[msg3_data m1.`1 b m1.`2 m2, cok]) (m1.`1, b);
    }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^k<- ~ {
      k <- prf (oget prfkey_map.[msg3_data m1.`1 b m1.`2 m2, m3]) (m1.`1, b);
    }
  ]
}.

(* Store keys in a map *)
module Game5 = Game4 with {
  var key_map : (trace, skey) fmap

  proc init_mem [-1 + { key_map <- empty; }]
  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^k<- ~ {
       k <$ dskey;
       key_map.[m1, m2, cok] <- k;
    }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^k<- ~ {
      k <- oget key_map.[m1, m2, m3];
    }
  ]
}.

(* Cleanup session state: don't store keys *)
module Game5a = Game5 with {
  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^key_map<- + { k <- witness; }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^k<- ~ { k <- witness; }
  ]
  proc reveal [
    [^if.^match#Accepted.^if.^state_map<- - ^ko<-] ~ {
      ko <- Some (oget key_map.[t]);
      state_map.[h] <- (r, Observed t (oget ko));
    }
  ]
  proc test [
    ^if.^match#Accepted.^if.^if.^k'<- ~ {
      k' <- oget key_map.[t];
    }
  ]
}.

(* Only sample and store keys in reveal/test queries *)
module Game5b = Game5a with {
  proc send_msg3 [
    [^if.^match#IPending.^match#Some.^if.^k<$ - ^key_map<-] -
  ]
  proc reveal [
    var k' : skey
    ^if.^match#Accepted.^if.1 ~ {
      k' <$ dskey;
      if (t \notin key_map) {
        key_map.[t] <- k';
      }
      ko <- key_map.[t];
    }
  ]
  proc test [
    ^if.^match#Accepted.^if.1 ~ {
      k' <$ dskey;
      if (t \notin key_map) {
        key_map.[t] <- k';
      }
      if (b0 = false) {
        k' <- oget key_map.[t];
      } else {
        k' <$ dskey;
      }
    }
  ]
}.

module Game5c = Game5b with {
  proc reveal [^if.^match#Accepted.^if.^if ~ { key_map.[t] <- k'; }]
  proc test [^if.^match#Accepted.^if.^if ~ { key_map.[t] <- k'; }]
}.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1 invariants *)

op Game1_inv (sm: (id * int, role * session_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
  (* Pending session state relation to psk map and well formedness of messages *)
  (forall a i r b psk na c1 m1, sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
   => pskm.[a, b] = Some psk /\ m1 = (a, c1))
  /\ (forall a i r b psk na nb c1 c2 m1 m2, sm.[a, i] = Some (r, RPending (b, psk, na, nb, c1, c2) m1 m2)
   => pskm.[b, a] = Some psk /\ m1 = (b, c1) /\ m2 = c2).

hoare Game1_inv_gen_pskey: Game1.gen_pskey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
if => //.
auto => /> *.
by split; smt(get_setE).
qed.

hoare Game1_inv_send_msg1: Game1.send_msg1:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proc; inline *.
sp; if => //.
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_send_msg2: Game1.send_msg2:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
by match; auto => />; smt(get_setE).
qed.

hoare Game1_inv_send_msg3: Game1.send_msg3:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; ~1: by auto.
by sp; match; auto => />; smt(get_setE).
qed.

hoare Game1_inv_send_fin: Game1.send_fin:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; ~2: by auto.
by sp; match; auto => />; smt(get_setE).
qed.

hoare Game1_inv_reveal: Game1.reveal:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; ~3: by auto.
auto => />.
smt(get_setE).
qed.

hoare Game1_inv_test: Game1.test:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==>
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; ~3: by auto.
if => //.
by if; auto => />; smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1a invariants *)

op Game1a_inv (sm: (id * int, role * session_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
  (* Pending session state relation to psk map and well formedness of messages *)
  (forall a i r b psk na c1 m1, sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
   => (m1.`1, b) \in pskm)
  /\ (forall b j r a psk na nb c1 c2 m1 m2, sm.[b, j] = Some (r, RPending (a, psk, na, nb, c1, c2) m1 m2)
   => (m1.`1, b) \in pskm). 

hoare Game1a_inv_gen_pskey: Game1a.gen_pskey:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
wp; if => //.
auto => />.
smt(mem_set).
qed.

hoare Game1a_inv_send_msg1: Game1a.send_msg1:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
auto => />.
smt(get_setE).
qed.

hoare Game1a_inv_send_msg2: Game1a.send_msg2:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
by sp; match; auto => />; smt(get_setE).
qed.

hoare Game1a_inv_send_msg3: Game1a.send_msg3:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match; ~1: auto.
by sp; match; auto => />; smt(get_setE).
qed.

hoare Game1a_inv_send_fin: Game1a.send_fin:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; ~2: by auto.
by sp; match; auto => />; smt(get_setE).
qed.

hoare Game1a_inv_reveal: Game1a.reveal:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => />.
smt(get_setE).
qed.

hoare Game1a_inv_test: Game1a.test:
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i)
==>
    (forall a i, Game1a_inv Game1a.state_map Game1a.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; ~3: by auto.
sp; if => //.
by sp; if; auto => />; smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 2 invariants *)

hoare Game2_inv_gen_pskey: Game2.gen_pskey:
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.gen_pskey ~ Game1a.gen_pskey: ={arg} /\ ={state_map, psk_map}(Game2, Game1a) ==> ={state_map, psk_map}(Game2, Game1a)] by sim />.
by conseq t Game1a_inv_gen_pskey=> /#.
qed.

hoare Game2_inv_send_msg1: Game2.send_msg1:
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
auto => />.
smt(get_setE).
qed.

hoare Game2_inv_send_msg2: Game2.send_msg2:
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
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
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match; ~1: by auto.
sp; match.
+ auto => />.
  smt(get_setE).
auto => />.
smt(get_setE).
qed.

hoare Game2_inv_send_fin: Game2.send_fin:
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
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
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.reveal ~ Game1a.reveal: ={arg} /\ ={state_map, psk_map}(Game2, Game1a) ==> ={state_map, psk_map}(Game2, Game1a)] by sim />.
by conseq t Game1a_inv_reveal => /#.
qed.

hoare Game2_inv_test: Game2.test:
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i)
==>
    (forall a i, Game1a_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.test ~ Game1a.test: ={arg} /\ ={b0, state_map, psk_map}(Game2, Game1a) ==> ={b0, state_map, psk_map}(Game2, Game1a)] by sim />.
by conseq t Game1a_inv_test => /#.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 3 invariants *)

op Game3_inv (sm: (id * int, role * session_state) fmap) (dm : (msg_data * ctxt, nonce) fmap) (a: id) (i: int) =
  (* Pending session state relation to dec map and well formedness of messages *)
  (forall a i r b psk na c1 m1, sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
      => dm.[msg1_data m1.`1 b, m1.`2] = Some na
      /\ m1.`1 = a)
  /\ (forall b j r a psk na nb c1 c2 m1 m2, sm.[b, j] = Some (r, RPending (a, psk, na, nb, c1, c2) m1 m2)
      => dm.[msg1_data m1.`1 b, m1.`2] = Some na
      /\ dm.[msg2_data m1.`1 b m1.`2, m2] = Some nb).

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
sp; match; ~1: by auto.
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
sp; match; ~2: by auto.
by sp; match; auto => />; smt(get_setE).
qed.

hoare Game3_inv_reveal: Game3.reveal:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==>
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; ~3: by auto.
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
sp; match; ~3: by auto.
sp; if => //.
by if; auto => />; smt(get_setE).
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 3d invariants *)

op Game3d_inv
  (sm: (id * int, role * session_state) fmap)
  (dm : (msg_data * ctxt, nonce) fmap)
  (nm : (msg_data * ctxt, nonce) fmap)
=
  (* Unicity of pending initiators *)
  (forall a i j c c' r r' b b' psk psk' na na' m1,
       sm.[(a, i)] = Some (r, IPending (b, psk, na, c) m1)
    => sm.[(a, j)] = Some (r', IPending (b', psk', na', c') m1)
    => i = j)

  (* Pending initiator state relationships *)
  /\ (forall a i r b psk na c1 m1,
        sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
        => a = m1.`1
        /\ (msg1_data m1.`1 b, m1.`2) \in dm
        /\ forall c2 c3, (msg3_data m1.`1 b m1.`2 c2, c3) \notin dm)

  /\ (forall a b m1 m2 m3, (msg3_data a b m1 m2, m3) \in dm
      => (msg1_data a b, m1) \in nm /\ (msg2_data a b m1, m2) \in nm)

  /\ (forall a b m1, (msg1_data a b, m1) \in nm
      => exists m2 m3, (msg3_data a b m1 m2, m3) \in dm)

  /\ (forall a b m1 m2, (msg2_data a b m1, m2) \in nm
      => exists m3, (msg3_data a b m1 m2, m3) \in dm)

  /\ (forall a b ca cb, (msg2_data a b ca, cb) \in dm => (msg1_data a b, ca) \in dm)

  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in dm => (msg2_data a b ca, cb) \in dm).

hoare Game3d_inv_send_msg1: Game3d.send_msg1:
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map)
  ==>
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map).
proof.
proc.
sp; wp; if=> //.
seq 1 : (#pre); 1: by auto.
case (Game3d.bad).
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

hoare Game3d_inv_send_msg2: Game3d.send_msg2:
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map)
  ==>
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map).
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

hoare Game3d_inv_send_msg3: Game3d.send_msg3:
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map)
  ==>
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map).
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
smt(get_setE).
qed.

hoare Game3d_inv_send_fin: Game3d.send_fin:
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map)
  ==>
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map).
proof.
proc.
sp; wp ^if; if=> //.
sp; match => //.
sp; match; auto; smt(get_setE).
qed.

hoare Game3d_inv_reveal: Game3d.reveal:
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map)
  ==>
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map).
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto=> />.
smt(get_setE).
qed.

hoare Game3d_inv_test: Game3d.test:
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map)
  ==>
  (Game3d_inv Game3d.state_map Game3d.dec_map Game3d.nonce_map).
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

op uniq_msg r s : ctxt option =
with r = Initiator => fst_msg s
with r = Responder => snd_msg s.

op Game5c_inv
  (sm: (id * int, role * session_state) fmap)
  (dm : (msg_data * ctxt, nonce) fmap)
  (skm : (trace, skey) fmap)
=
(* Unicity of sessions *)
   (forall c r h st h' st',
    sm.[h] = Some (r, st) /\ sm.[h'] = Some (r, st')
    /\ uniq_msg r st = Some c
    /\ uniq_msg r st' = Some c
    => h = h')

(* Session state well-formedness and log relationship *)
/\ (forall a i r b psk na c1 m1,
      sm.[a, i] = Some (r, IPending (b, psk, na, c1) m1)
      => (msg1_data m1.`1 b, m1.`2) \in dm
      /\ r = Initiator /\ m1.`1 = a)

/\ (forall b j r a psk na nb c1 c2 m1 m2,
      sm.[b, j] = Some (r, RPending (a, psk, na, nb, c1, c2) m1 m2)
      => (msg1_data m1.`1 b, m1.`2) \in dm /\ (msg2_data m1.`1 b m1.`2, m2) \in dm
      /\ r = Responder)

/\ (forall a i r b m1 m2 m3 sk,
      sm.[a, i] = Some (r, Accepted ((b, m1), m2, m3) sk)
      => (exists ad, (ad, m1) \in dm) /\ (exists ad, (ad, m2) \in dm))

/\ (forall a i r b m1 m2 m3 sk,
      sm.[a, i] = Some (r, Observed ((b, m1), m2, m3) sk)
      => (exists ad, (ad, m1) \in dm) /\ (exists ad, (ad, m2) \in dm))

(* SK implies existence of an observed session *)
/\ (forall t, t \in skm => exists a i r k, sm.[a, i] = Some (r, Observed t k)).

hoare Game5c_inv_send_msg1: Game5c.send_msg1:
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map
  ==>
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map.
proof.
proc.
sp; wp; if=> //.
seq 1 : (#pre); 1: by auto.
auto => />.
move => &m uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs sm psk bad.
do! split; ~1:smt(get_setE).
(* Fresh ciphertext implies not in log *)
move => c r h st h' st'.
rewrite !get_setE.
case (h = (a, i){m}).
+ case (h' = (a, i){m}) => //.
  smt(get_setE).
case (h' = (a, i){m}) => //. 
+ move => />.
  smt(get_setE).
smt().
qed.

hoare Game5c_inv_send_msg2: Game5c.send_msg2:
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map
  ==>
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map.
proof.
proc.
sp; wp; if=> //.
sp; match => //.
+ auto=> />.
  move => &m dm sm uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs smnin.
  do! split; smt(get_setE).
seq 1 : (#pre); 1: by auto.
auto => />.
move => &m dm sm uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs smnin bad.
do! split; ~1: smt(get_setE).
(* Fresh ciphertext implies not in log *)
move => c r h st h' st'.
rewrite !get_setE.
case (h = (b, j){m}).
+ case (h' = (b, j){m}) => //.
  smt(get_setE).
case (h' = (b, j){m}) => //. 
+ move => />.
  smt(get_setE).
smt().
qed.

hoare Game5c_inv_send_msg3: Game5c.send_msg3:
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map
  ==>
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map.
proof.
proc.
sp; wp; if=> //.
sp; match => //.
sp; match => //.
+ auto => />.
  move => &m dm sm uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs smin.
  do! split; smt(get_setE).
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto=> />.
move => &m _ dm sm uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in /negb_or [_ uniq] nok _ na _ nb _.
do! split; ~1,5: smt(get_setE).
+ move => c r h st h' st'.
  have := uniq_pi ca{m} Initiator (a, i){m}.
  case (h = (a, i){m}) => />.
  + smt(get_setE).
  case (h' = (a, i){m}) => />.
  + smt(get_setE).
  smt(get_setE).
move => a0 i0 r b' m1' m2' m3' sk.
rewrite get_setE.
by case ((a0, i0) = (a, i){m}); smt(mem_set).
qed.

hoare Game5c_inv_send_fin: Game5c.send_fin:
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map
  ==>
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map.
proof.
proc.
sp; wp ^if; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  move => *.
  do! split; smt(get_setE).
auto => />.
move => &m dm sm uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in.
do! split; ~1,4:smt(get_setE).
+ move => c r h st h' st'.
  have := uniq_pi m2{m} Responder (b, j){m}.
  case (h = (b, j){m}) => />.
  + smt(get_setE).
  case (h' = (b, j){m}) => />.
  + smt(get_setE).
  smt(get_setE).
move => v x r b' m1' m2' m3' sk.
rewrite get_setE.
by case ((v, x) = (b, j){m}) => /#.
qed.

hoare Game5c_inv_reveal: Game5c.reveal:
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map
  ==>
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
auto => />.
move => &m smai uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps k n _.
do! split; ~5,6: smt(get_setE).
+ move => a0 i0 r b m1 m2 m3 sk.
  rewrite get_setE.
  by case ((a0, i0) = h{m}) => /#.
move => t.
rewrite mem_set.
case; smt(get_setE).
qed.

hoare Game5c_inv_test: Game5c.test:
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map
  ==>
  Game5c_inv Game5c.state_map Game5c.dec_map Game5c.key_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.  
sp; if => //.
case (Game5c.b0).
+ rcondf ^if; 1: by auto => />.
  auto => />.
  move => &m sm smai uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps _ k _ k' _.
  do! split; ~5,6: smt(get_setE).
  + move => a0 i0 r b m1 m2 m3 sk.
    rewrite get_setE.
    by case ((a0, i0) = h{m}) => /#.
  move => t.
  rewrite mem_set.
  case; smt(get_setE).
rcondt ^if; 1: by auto => />.
auto => />.
move => &m sm smai uniq_pi ss_log_ip ss_log_rp ss_log_acc ss_log_obs sk_obs ai_in obs_ps _ k _.
do! split; ~5,6: smt(get_setE).
+ move => a0 i0 r b m1 m2 m3 sk.
  rewrite get_setE.
  by case ((a0, i0) = h{m}) => /#.
move => t.
rewrite mem_set.
case; smt(get_setE).
qed.
