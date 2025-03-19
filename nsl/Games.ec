require import AllCore FMap FSet Distr NSL List.
import GWAKEc AEADc.

(* ------------------------------------------------------------------------------------------ *)
(* Intermediate Games *)
(* ------------------------------------------------------------------------------------------ *)

type log_entry = [
  | GenPskey of (id * id)
  | SendMsg1 of (id * int * id) & ctxt option
  | SendMsg2 of (id * int * (id * ctxt)) & ctxt option
  | SendMsg3 of (id * int * ctxt) & ctxt option
  | SendFin of (id * int * ctxt) & unit option
  | RevSkey of (id * int) & skey option
  | Test of (id * int) & skey option
].

op get_message e : ctxt option =
with e = GenPskey _ => None
with e = SendMsg1 _ co => co
with e = SendMsg2 _ co => co
with e = SendMsg3 _ co => co
with e = SendFin _ _ => None
with e = RevSkey _ _ => None
with e = Test _ _ => None.

(* Inlining and removing psk from instance state *)
module Game1 = {
  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap
  var log: log_entry list

  proc init_mem() : unit = {
    state_map <- empty;
    psk_map <- empty;
    log <- [];
  }

  proc gen_pskey(a: id, b: id) : unit = {
    var k;
    if ((a, b) \notin psk_map) {
      k <$ dpskey;
      psk_map.[(a, b)] <- k;
    }
    log <- GenPskey (a, b) :: log;
  }
  
  proc send_msg1(a, i, b) = {
    var na, ca;
    var mo <- None;
 
    if ((a, i) \notin state_map /\ (a, b) \in psk_map) {
      na <$ dnonce;
      ca <$ enc (oget psk_map.[(a, b)]) (msg1_data a b) na;
      mo <- Some ca;
      state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, ca) (a, ca));
    }
    log <- SendMsg1 (a, i, b) mo :: log;
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
        state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, cb) m1 cb);
      } else {
        state_map.[(b, j)] <- (Responder, Aborted);
      }
    }
    log <- SendMsg2 (b, j, m1) mo :: log;
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
          state_map.[(a, i)] <- (Initiator, Accepted ((a, ca), m2, caf) skey);
         } else {
          state_map.[(a, i)] <- (Initiator, Aborted);
        }
      }
    }
    log <- SendMsg3 (a, i, m2) mo :: log;
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
    log <- SendFin (b, j, m3) mo :: log;
    return mo;
  }

  proc rev_skey(a, i) = {
    var role, st, ps, k;
    var ko <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      match st with
      | Accepted trace k' => {
        ps <- get_partners (a, i) (Some trace) role state_map;
        if (card ps <= 1) {
          ps <- get_observed_partners (a, i) state_map;
          if (card ps = 0) {
            k <- k';
            ko <- Some k;
            state_map.[(a, i)] <- (role, Observed trace k);
          }
        }
      }
      | Observed _ _   => { }
      | IPending _ _   => { }
      | RPending _ _ _ => { }
      | Aborted        => { }
      end;
    }
    log <- RevSkey (a, i) ko :: log;
    return ko;
  }
 
  proc test(a, i) = {
    var role, st, ps, k;
    var ko <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      match st with
      | Accepted trace k' => {
        ps <- get_partners (a, i) (Some trace) role state_map;
        if (card ps <= 1) {
          ps <- get_observed_partners (a, i) state_map;
          if (card ps = 0) {
            k <- k';
            ko <- Some k;
            state_map.[(a, i)] <- (role, Observed trace k);
          }
        }
      }
      | Observed _ _   => { }
      | IPending _ _   => { }
      | RPending _ _ _ => { }
      | Aborted        => { }
      end;
    }
    log <- Test (a, i) ko :: log;
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

print Game2.

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

print Game6.

module Game7 = Game6 with {
  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^sk_map<- + { skey <- witness; }
  ]
  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ { skey <- witness; }
  ]
  proc rev_skey [
    ^if.^match#Accepted.^if.^if.^k<- ~ {
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
  proc test [
    ^if.^match#Accepted.^if.^if.^k<- ~ { k <$ dskey; }
  ]
}.
(* ------------------------------------------------------------------------------------------ *)
(* Game 0 invariants *)

inductive GWAKE0_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
| GWAKE0_undef of
    (sm.[a, i] = None)
| GWAKE0_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| GWAKE0_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & (pskm.[a, b] = Some kab)
| GWAKE0_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & (pskm.[b, a] = Some kba)
| GWAKE0_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| GWAKE0_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma GWAKE0_inv_neq a i c j v sm psk:
! (c = a /\ j = i) =>
GWAKE0_inv sm psk c j =>
GWAKE0_inv sm.[(a, i) <- v] psk c j.
proof.
move=> neq
[
smbj
| r smbj
| b na c1 kab smbj pskcb
| b na nb c1 c2 kba smbj pskcb
| r tr k smbj
| r tr k smbj
].
+ apply GWAKE0_undef.
  by rewrite get_set_neqE.
+ apply (GWAKE0_aborted _ _ _ _ r).
  by rewrite get_set_neqE.
+ apply (GWAKE0_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ apply (GWAKE0_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ apply (GWAKE0_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
apply (GWAKE0_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

hoare GWAKE0_inv_gen_pskey: GWAKE0(NSL).gen_pskey:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
if => //.
auto => />.
move => &m inv abnin pk _ a' i'.
case: (inv a' i') =>
[ 
smbj
| r smbj
| b na c1 kab smbj pskcb
| b na nb c1 c2 kba smbj pskcb
| r tr k smbj
| r tr k smbj
].
+ exact GWAKE0_undef.
+ exact (GWAKE0_aborted _ _ _ _ r).
+ apply (GWAKE0_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).  
+ apply (GWAKE0_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  smt(get_setE).
+ exact (GWAKE0_accepted _ _ _ _ r tr k).
exact (GWAKE0_observed _ _ _ _ r tr k).
qed.
    
lemma GWAKE0_inv_aborted a i b j r sm pm: GWAKE0_inv sm pm a i => GWAKE0_inv sm.[(b, j) <- (r, Aborted)] pm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (GWAKE0_aborted _ _ _ _ r).
  by rewrite get_set_sameE.
exact /GWAKE0_inv_neq/inv.
qed.

hoare GWAKE0_inv_send_msg1: GWAKE0(NSL).send_msg1:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proc; inline *.
sp; if => //.
auto => /> &m inv ainin /domE abin na _ ca _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (GWAKE0_ipending _ _ _ _ b{m} na ca (oget GWAKEb.psk_map.[(a, b)]{m})).
  - by rewrite get_set_sameE.
  exact some_oget.
exact /GWAKE0_inv_neq/inv.
qed.
    
hoare GWAKE0_inv_send_msg2: GWAKE0(NSL).send_msg2:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ match None ^match; 1: by auto.
  auto => /> &m decn st inv bjnin abin a' i'.
  exact /GWAKE0_inv_aborted/inv.
match Some ^match; 1: by auto=> /#.
auto => /> &m decn st inv bjnin /domE abin n _ cb0 cin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKE0_rpending _ _ _ _ a0{m} na{m} n ca{m} cb0 (oget GWAKEb.psk_map.[(a0, b)]{m})).
  - by rewrite get_set_sameE.
  exact some_oget.
exact /GWAKE0_inv_neq/inv.
qed.

hoare GWAKE0_inv_send_msg3: GWAKE0(NSL).send_msg3:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: by auto.
sp; match.
- match None ^match; 1: by auto.
  auto => /> &m decn st inv aiin a' i'.
  exact /GWAKE0_inv_aborted/inv.
match Some ^match; 1: auto => /#.
auto => /> &m decn st inv aiin n _ ca0 cin a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKE0_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
exact /GWAKE0_inv_neq/inv.
qed.

hoare GWAKE0_inv_send_fin: GWAKE0(NSL).send_fin:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
- match None ^match; 1: by auto.
  auto => /> &m decn st inv bjin a' i'.
  exact /GWAKE0_inv_aborted/inv.
match Some ^match; 1: auto => /#.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKE0_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
exact /GWAKE0_inv_neq/inv.
qed.

hoare GWAKE0_inv_rev_skey: GWAKE0(NSL).rev_skey:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (GWAKE0_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /GWAKE0_inv_neq/inv.
qed.

hoare GWAKE0_inv_test: GWAKE0(NSL).test:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (GWAKE0_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /GWAKE0_inv_neq/inv.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1 invariants *)

inductive Game1_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
| Game1_undef of
    (sm.[a, i] = None)
| Game1_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| Game1_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & ((a, b) \in pskm)
| Game1_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & ((b, a) \in pskm)
| Game1_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| Game1_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma Game1_inv_neq a i c j v sm psk:
! (c = a /\ j = i) =>
Game1_inv sm psk c j =>
Game1_inv sm.[(a, i) <- v] psk c j.
proof.
move=> neq
[ 
smbj
| r smbj
| b na c1 kab smbj pskcb
| b na nb c1 c2 kba smbj pskcb
| r tr k smbj
| r tr k smbj
].
+ apply Game1_undef.
  by rewrite get_set_neqE.
+ apply (Game1_aborted _ _ _ _ r).
  by rewrite get_set_neqE.
+ apply (Game1_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ apply (Game1_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ apply (Game1_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
apply (Game1_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

lemma Game1_inv_aborted a i b j r sm pm: Game1_inv sm pm a i => Game1_inv sm.[(b, j) <- (r, Aborted)] pm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (Game1_aborted _ _ _ _ r).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game1_inv_gen_pskey: Game1.gen_pskey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
wp; if => //.
auto => />.
move => &m inv abnin pk _ a' i'.
case: (inv a' i') =>
[ 
smbj
| r smbj
| b na c1 kab smbj pskcb
| b na nb c1 c2 kba smbj pskcb
| r tr k smbj
| r tr k smbj
].
+ exact Game1_undef.
+ exact (Game1_aborted _ _ _ _ r).
+ apply (Game1_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite mem_set pskcb.
+ apply (Game1_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  by rewrite mem_set pskcb.
+ exact (Game1_accepted _ _ _ _ r tr k).
exact (Game1_observed _ _ _ _ r tr k).
qed.
    
hoare Game1_inv_send_msg1: Game1.send_msg1:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
auto => /> &m inv ainin abin na _ ca _ a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
+ apply (Game1_ipending _ _ _ _ b{m} na ca witness)=> //.
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.
    
hoare Game1_inv_send_msg2: Game1.send_msg2:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv bjnin abin n _ cb0 cin a' i'.
case ((a', i') = (b, j){m}) => [[] <<- <-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_rpending _ _ _ _ a{m} na{m} n ca{m} cb0 witness) => //.
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
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
+ auto => /> &m decn st inv abin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv aiin n _ ca0 cin a' i'.
case ((a', i') = (a, i){m}) => [<-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Initiator ((a, ca){m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
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
- auto => /> &m decn st inv bjin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [<-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Responder ((a, ca){m}, cb{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
exact /Game1_inv_neq/inv.
qed.

hoare Game1_inv_rev_skey: Game1.rev_skey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game1_inv_test: Game1.test:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
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
auto => /> &m inv ainin abin ca _ na _ a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <- |neq_ai].
+ apply (Game1_ipending _ _ _ _ b{m} na ca witness) => //.
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.
    
hoare Game2_inv_send_msg2: Game2.send_msg2:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv bjnin abin cb0 _ n cin a' i'.
case ((a', i') = (b, j){m}) => [[] <<- <-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_rpending _ _ _ _ a{m} na{m} n ca{m} cb0 witness) => //.
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
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
+ auto => /> &m decn st inv abin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv aiin ca0 _ n cin a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Initiator ((a', ca{m}), m2{m}, ca0) (prf (na{m}, nb{m}) (a', b{m}))).
  by rewrite get_set_sameE. 
exact /Game1_inv_neq/inv.
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
- auto => /> &m decn st inv bjin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [[] <<- <-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Responder ((a, ca){m}, cb{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, a'))).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game2_inv_rev_skey: Game2.rev_skey:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.rev_skey ~ Game1.rev_skey: ={arg} /\ ={state_map, psk_map}(Game2, Game1) ==> ={state_map, psk_map}(Game2, Game1)] by sim />.
by conseq t Game1_inv_rev_skey => /#.
qed.

hoare Game2_inv_test: Game2.test:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
have t: equiv[Game2.test ~ Game1.test: ={arg} /\ ={state_map, psk_map}(Game2, Game1) ==> ={state_map, psk_map}(Game2, Game1)] by sim />.
by conseq t Game1_inv_test => /#.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 3 invariants *)
inductive Game3_inv 
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (a: id) (i: int)
=
| Game3_undef of
    (sm.[a, i] = None)
| Game3_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| Game3_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & (dm.[((a, b), msg1_data a b, c1)] = Some na)
| Game3_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & (dm.[((b, a), msg1_data b a, c1)] = Some nb)
  & (dm.[((b, a), msg2_data b a c1, c2)] = Some na)
| Game3_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| Game3_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma Game3_inv_neq_sm a i c j v sm dm:
! (c = a /\ j = i) =>
Game3_inv sm dm c j =>
Game3_inv sm.[(a, i) <- v] dm c j.
proof.
move=> neq
[ 
  smbj
| r smbj
| b na c1 kab smbj dmcb
| b na nb c1 c2 kba smbj dmcb
| r tr k smbj
| r tr k smbj
].
+ apply Game3_undef.
  by rewrite get_set_neqE.
+ apply (Game3_aborted _ _ _ _ r).
  by rewrite get_set_neqE.
+ apply (Game3_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ apply (Game3_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ apply (Game3_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
apply (Game3_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

lemma Game3_inv_neq_dm a i c n sm (dm : (_, _) fmap):
! (exists pk ad, (pk, ad, c) \in dm) =>
Game3_inv sm dm a i =>
forall pk ad, Game3_inv sm dm.[(pk, ad, c) <- n] a i.
proof.
move=> neq
[ 
  smbj pk ad
| r smbj pk ad
| b na c1 kab smbj dmcb pk ad
| b na nb c1 c2 kba smbj dmnb dmna pk ad
| r tr k smbj pk ad
| r tr k smbj pk ad
].
+ exact Game3_undef.
+ exact (Game3_aborted _ _ _ _ r).
+ apply (Game3_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).  
+ apply (Game3_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  + smt(get_setE).  
  smt(get_setE).  
+ exact (Game3_accepted _ _ _ _ r tr k).
exact (Game3_observed _ _ _ _ r tr k).
qed.

lemma Game3_inv_aborted a i b j r sm dm: Game3_inv sm dm a i => Game3_inv sm.[(b, j) <- (r, Aborted)] dm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (Game3_aborted _ _ _ _ r).
  by rewrite get_set_sameE.
exact /Game3_inv_neq_sm/inv. 
qed.

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
auto => /> &m _ inv ainin abin /negb_or [_ uniq] na _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ by apply (Game3_ipending _ _ _ _ b{m} na ca{m} witness); rewrite get_set_sameE.
exact /Game3_inv_neq_sm/Game3_inv_neq_dm/inv.
qed.
    
hoare Game3_inv_send_msg2: Game3.send_msg2:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  exact /Game3_inv_aborted/inv.
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto => /> &m _ decn st inv bjnin abin /negb_or [_ bad] n _ a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ apply (Game3_rpending _ _ _ _ a{m} na{m} n ca{m} cb{m} witness).
  - by rewrite get_set_sameE.
  - by rewrite get_set_neqE //= decn. 
  by rewrite get_set_sameE.
exact /Game3_inv_neq_sm/Game3_inv_neq_dm/inv.
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
+ auto => /> &m decn st inv abin a' i'.
  exact /Game3_inv_aborted/inv.
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto => /> &m _ decn st inv aiin /negb_or [_ bad] ok _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (Game3_accepted _ _ _ _ Initiator ((a, ca){m}, m2{m}, caf{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
exact /Game3_inv_neq_sm/Game3_inv_neq_dm/inv.
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
- auto => /> &m decn st inv bjin a' i'.
  exact /Game3_inv_aborted/inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ apply (Game3_accepted _ _ _ _ Responder ((a, ca){m}, cb{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
exact /Game3_inv_neq_sm/inv.
qed.

hoare Game3_inv_rev_skey: Game3.rev_skey:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /Game3_inv_neq_sm/inv.
qed.

hoare Game3_inv_test: Game3.test:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /Game3_inv_neq_sm/inv.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 5 invariants *)
inductive Game5_inv 
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (nm : (msg_data * ctxt, nonce * nonce) fmap)
  (a: id) (i: int)
=
| Game5_undef of
    (sm.[a, i] = None)
| Game5_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| Game5_ipending b c1 of
    (sm.[a, i] = Some (Initiator, IPending (b, witness, witness, c1) (a, c1)))
  & (((a, b), msg1_data a b, c1) \in dm)
  & (forall c2 c3, (msg3_data a b c1 c2, c3) \notin nm)
| Game5_rpending b c1 c2 of
    (sm.[a, i] = Some (Responder, RPending (b, witness, witness, witness, c1, c2) (b, c1) c2))
| Game5_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| Game5_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).
   
op Game5_inv_full
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (nm : (msg_data * ctxt, nonce * nonce) fmap)
=
  ((forall a i j b c, 
       sm.[(a, i)] = Some (Initiator, IPending (b, witness, witness, c) (a, c))
    /\ sm.[(a, j)] = Some (Initiator, IPending (b, witness, witness, c) (a, c))
    => i = j)
  /\ (forall a b ca cb, ((a, b), msg2_data a b ca, cb) \in dm => ((a, b), msg1_data a b, ca) \in dm)
  /\ (forall a b ca cb caf, ((a, b), msg3_data a b ca cb, caf) \in dm => ((a, b), msg2_data a b ca, cb) \in dm)
  /\ (forall a b ca cb caf, (msg3_data a b ca cb, caf) \in nm <=> ((a, b), msg3_data a b ca cb, caf) \in dm))
  /\ (forall a i, Game5_inv sm dm nm a i).

abbrev "_.[_]" = List.nth witness<: 'a>.

op Game5_inv_log (log : log_entry list)
= 
(forall b j a i m2 m3 s, log.[s] = SendFin (b, j, m3) (Some tt) =>
  exists t, s < t /\ log.[t] = SendMsg3 (a, i, m2) (Some m3))
/\
(forall b j a i m1 m2 m3 s, log.[s] = SendMsg3 (a, i, m2) (Some m3) =>
  exists t, s < t /\ log.[t] = SendMsg2 (b, j, m1) (Some m2))
/\
(forall b j a i m1 m2 s, log.[s] = SendMsg2 (b, j, (a, m1)) (Some m2) =>
  exists t, s < t /\ log.[t] = SendMsg1 (a, i, b) (Some m1))
/\
(forall s m, m = oget (get_message log.[s]) => forall t, m = oget (get_message log.[t]) => s = t).

op Game5_inv_bind_log 
  (log : log_entry list)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap) 
=
  ((forall a i b m1, (exists t, 0 <= t /\ log.[t] = SendMsg1 (a, i, b) (Some m1)) <=> ((a, b), msg1_data a b, m1) \in dm)
  /\ (forall a b j m1 m2, (exists t, 0 <= t /\ log.[t] = SendMsg2 (b, j, (a, m1)) (Some m2)) <=> ((a, b), msg2_data a b m1, m2) \in dm)
  /\ (forall a i b m1 m2 m3, (exists t, 0 <= t /\ log.[t] = SendMsg3 (a, i, m2) (Some m3)) <=> ((a, b), msg3_data a b m1 m2, m3) \in dm)).

hoare Game5_inv_log_send_msg2: Game5.send_msg2:
  (Game5_inv_log Game5.log /\ Game5_inv_bind_log Game5.log Game5.dec_map)
  ==>
  (Game5_inv_log Game5.log /\ Game5_inv_bind_log Game5.log Game5.dec_map).
proof.
proc.
sp; wp; if=> //.
+ match => //.
  + auto => />.
    admit. (* later *)
  seq 1 : (#pre); 1: by auto.
  sp 1; if => //.
  + auto => /> &m /> bad H ? fin_inv msg3_inv msg2_inv uniq_inv bind_msg1 bind_msg2 bind_msg3 ? ? ?.
    split. 
    (* first log invariant *)
    + split.
      + move => b j a i m2 m3 s.
        case (s = 0) => />.
        case (s < 0); 1: smt(nth_out).
        move => sneq0 sge0 /fin_inv /(_ a i m2) [] t [slet <-].
        exists (t+1); smt().
      split.
      + move => b j a i m1 m2 m3 s.
        case (s = 0) => />.
        case (s < 0); 1: smt(nth_out).
        move => sneq0 sge0 /msg3_inv /(_ b j m1) [] t [slet <-].
        exists (t+1); smt().
      split.
      + move => b j a i m1 m2 s.
        case (s = 0) => />.
        + have := bind_msg1 a{!m} i b{!m} ca{m}.
          have : ((a{!m}, b{!m}), msg1_data a{!m} b{!m}, ca{m}) \in Game5.dec_map{m}.
          + rewrite fmapP H.
            by exists na{m}.
          move => /> _ t le0t <-.
          exists (t+1) => //=. 
          smt().
        case (s < 0); 1: smt(nth_out).
        move => sneq0 sge0 /msg2_inv /(_ i) [] t [slet <-].
        exists (t+1); smt().
      move => s t.
      case (s = 0).
      + case (t = 0); 1: smt().
        move => tneq0 seq0.
        admit. (* need that cb is unique *)
      case (t = 0); 2: smt().
      move => teq0 sneq0.
      admit. (* need that cb is unique *)
    (* next binding invariant *)
    split; 1: smt(get_setE).
    split. 
    + move => a b j m1 m2.
      split; 1: smt(get_setE mem_set).   
      rewrite mem_set.
      case ((((a, b), msg2_data a b m1, m2) \in Game5.dec_map{m})); 1: smt().
      move => nindm //= equals.
      exists 0 => //=.      
      admit. (* How to prove that j = j{m}? *)
    smt(get_setE).
  skip => />. 
  admit. (* later *)
skip => />.
admit. (* later *)
qed. 

lemma Game5_inv_neq_sm a i c j v sm dm nm:
! (c = a /\ j = i) =>
Game5_inv sm dm nm c j =>
Game5_inv sm.[(a, i) <- v] dm nm c j.
proof.
move=> neq
[ 
  smbj
| r smbj
| b c1 smbj
| b c1 c2 smbj
| r tr k smbj
| r tr k smbj
].
+ apply Game5_undef.
  by rewrite get_set_neqE.
+ apply (Game5_aborted _ _ _ _ _ r).
  by rewrite get_set_neqE.
+ apply (Game5_ipending _ _ _ _ _ b c1) => //.
  by rewrite get_set_neqE.
+ apply (Game5_rpending _ _ _ _ _ b c1 c2)=> //.
  by rewrite get_set_neqE.
+ apply (Game5_accepted _ _ _ _  _ r tr k)=> //.
  by rewrite get_set_neqE.
apply (Game5_observed _ _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

lemma Game5_inv_neq_dm a i m sm (dm : (_, _) fmap) nm:
! (exists pk ad, (pk, ad, m) \in dm) =>
Game5_inv sm dm nm a i =>
forall pk ad, Game5_inv sm dm.[(pk, ad, m) <- witness] nm a i.
proof.
move=> neq
[ 
  smbj
| r smbj
| b c1 smbj v1 v2
| b c1 c2 smbj
| r tr k smbj
| r tr k smbj
] pk ad.
+ exact Game5_undef.
+ exact (Game5_aborted _ _ _ _ _ r).
+ apply (Game5_ipending _ _ _ _ _ b c1) => //.
  by rewrite mem_set v1.  
+ exact (Game5_rpending _ _ _ _ _ b c1 c2).
+ exact (Game5_accepted _ _ _ _  _ r tr k).
exact (Game5_observed _ _ _ _ _ r tr k).
qed.

lemma Game5_inv_aborted a i b j r sm dm nm: Game5_inv sm dm nm a i => Game5_inv sm.[(b, j) <- (r, Aborted)] dm nm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (Game5_aborted _ _ _ _ _ r).
  by rewrite get_set_sameE.
exact /Game5_inv_neq_sm/inv. 
qed.

hoare Game5_inv_send_msg1: Game5.send_msg1:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp; if=> //.
seq 1 : (#pre); 1: by auto.
case (Game5.bad).
+ by rcondf ^if; auto=> />.
auto=> />.
move=> &m inv1 inv2 inv3 inv4 inv5 ainin abin _ canin.
split.
+ split; 2: smt(get_setE).
  move=> a' i' j b' c.
  rewrite !get_setE //=.
  case: (a' = a{m}) => />; last by smt().
  case: (i' = i{m}) => />.
  + case: (j = i{m}) => />.
    move=> neqji smj.
    case: (inv5 a{m} j); rewrite smj //=.
    smt().
  move=> neqi'i smi.
  case: (inv5 a{m} i'); rewrite smi //=.
  smt().
move=> a i.
case: ((a, i) = (a, i){!m}) => /> => [| neq].
+ apply (Game5_ipending _ _ _ _ _ b{m} ca{m}).
  + by rewrite get_set_sameE.
  + by rewrite mem_set.
  move=> c2 c3.
  by rewrite inv4 /#.
exact /Game5_inv_neq_sm/Game5_inv_neq_dm/inv5.
qed.

hoare Game5_inv_send_msg2: Game5.send_msg2:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp; if=> //.
sp; match => //.
+ auto=> />.
  move=> &m dm sm inv1 inv2 inv3 inv4 inv5 bjnin abin.
  split; 1: smt(get_setE).
  move=> b j.
  exact /Game5_inv_aborted/inv5.
seq 1 : (#pre); 1: by auto.
auto=> />.
move=> &m dm sm inv1 inv2 inv3 inv4 inv5 bjnin abin /negb_or [_ cbnin].
split; 1: smt(mem_set get_setE).
move=> b j.
case: ((b, j) = (b, j){!m}) => /> => [|neq_ai].
- apply (Game5_rpending _ _ _ _ _ a{m} ca{m} cb{m}).
  by rewrite get_set_sameE. 
exact /Game5_inv_neq_sm/Game5_inv_neq_dm/inv5.
qed.

hoare Game5_inv_send_msg3: Game5.send_msg3:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  move=> &m dm sm inv1 inv2 inv3 inv4 inv5 aiin.
  split; 1: smt(get_setE).
  move=> a i.
  exact /Game5_inv_aborted/inv5.
seq 1 : (#pre); 1: by auto.
sp; if=> //.
auto=> />.
move=> &m _ dm sm inv1 inv2 inv3 inv4 inv5 /domE aiin /negb_or [_ cafnin] ns _.
split; 1: smt(mem_set get_setE).
move=> a' i'.
case: ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_accepted _ _ _ _ _ Initiator ((a, ca), m2, caf){m} (prf (ns.`1, ns.`2) (a, b)){!m}).
  by rewrite get_set_sameE. 
apply /Game5_inv_neq_sm/Game5_inv_neq_dm => //=.
case: (inv5 a' i') =>
[ 
  smai
| r smai
| b c1 smai' v1 v2
| b c1 c2 smai
| r tr k smai
| r tr k smai
].
+ exact Game5_undef.
+ exact (Game5_aborted _ _ _ _ _ r).
+ apply (Game5_ipending _ _ _ _ _ b c1) => //.
  move=> c2 c3.
  have smai : Game5.state_map{m}.[(a, i){m}] = Some (role{m}, IPending (b{!m}, psk{m}, na{m}, ca{m}) m1{m}).
  + by rewrite some_oget //= -sm.
  case: (inv5 a{m} i{m}); rewrite smai //=.
  smt(mem_set).
+ exact (Game5_rpending _ _ _ _ _ b c1 c2).
+ exact (Game5_accepted _ _ _ _  _ r tr k).
exact (Game5_observed _ _ _ _ _ r tr k).
qed.

hoare Game5_inv_send_fin: Game5.send_fin:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp ^if; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  move=> &m dm sm inv1 inv2 inv3 inv4 inv5 bjin.
  split; 1: smt(get_setE).
  move=> b j.
  exact /Game5_inv_aborted/inv5.
auto=> />.
move=> &m dm sm inv1 inv2 inv3 inv4 inv5 /domE bjin.
split; 1: smt(get_setE).
move=> b' j'.
case ((b', j') = (b, j){m}) => /> => [|neq_bj].
- apply (Game5_accepted _ _ _ _ _ Responder ((a, ca), cb, m3){m} (prf (oget Game5.prfkey_map{m}.[(msg3_data a{m} b{m} ca{m} cb{m}, m3{m})]) (a, b)){m}).
  by rewrite get_set_sameE. 
exact /Game5_inv_neq_sm/inv5. 
qed.

hoare Game5_inv_rev_skey: Game5.rev_skey:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv1 inv2 inv3 inv4 inv5 aiin _ _.
split; 1: smt(get_setE).
move=> a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_observed _ _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /Game5_inv_neq_sm/inv5.
qed.

hoare Game5_inv_test: Game5.test:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv1 inv2 inv3 inv4 inv5 aiin _ _.
split; 1: smt(get_setE).
move=> a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_observed _ _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /Game5_inv_neq_sm/inv5.
qed.
