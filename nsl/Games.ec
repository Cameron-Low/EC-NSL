require import AllCore FMap FSet Distr NSL.
import GWAKEc AEADc.

(* ------------------------------------------------------------------------------------------ *)
(* Intermediate Games *)
(* ------------------------------------------------------------------------------------------ *)

(* Inlining and removing psk from instance state *)
module Game1 = {
  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap

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
  
  proc send_msg1(a, i, b) = {
    var na, ca;
    var mo <- None;
 
    if ((a, i) \notin state_map /\ (a, b) \in psk_map) {
      na <$ dnonce;
      ca <$ enc (oget psk_map.[(a, b)]) (msg1_data a b) na;
      mo <- Some ca;
      state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, ca) (a, ca));
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
        if (dec (oget psk_map.[(a, b)]) (msg2_data a b ca) m2 is Some nb) {
          ok <$ dnonce;
          caf <$ enc (oget psk_map.[(a, b)]) (msg3_data a b ca m2) ok;
          mo <- Some caf;
          skey <- prf (na, nb) (a, b);
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
        if (dec (oget psk_map.[(a, b)]) (msg3_data a b ca cb) m3 is Some nok) {
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
}.

(* Decmap instead of real enc/dec *)
module Game2 = Game1 with {
  var dec_map: ((id * id) * msg_data * ctxt, nonce) fmap
  var bad : bool
  
  proc init_mem [
    -1 + { dec_map <- empty; },
    -1 + { bad <- false; }
  ]
  
  proc send_msg1 [
    ^if.^na<$ -,
    ^if.^ca<$ ~ {
      ca <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, ca) \in dec_map;
      na <$ dnonce;
      dec_map.[((a,b), msg1_data a b, ca)] <- na;
     }
  ]

  proc send_msg2 [
    ^if.^match ~ (dec_map.[((a, b), msg1_data a b, ca)]),
    ^if.^match#Some.^nb<$ -,
    ^if.^match#Some.^cb<$ ~ {
      cb <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, cb) \in dec_map;
      nb <$ dnonce;
      dec_map.[((a,b), msg2_data a b ca, cb)] <- nb;
     }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match ~ (dec_map.[((a, b), msg2_data a b ca, m2)]),
    ^if.^match#IPending.^match#Some.^ok<$ -,
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
    ^if.^bad<- + (!bad)
  ]

  proc send_msg2 [
    ^if.^match#Some.^bad<- + (!bad)
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^bad<- + (!bad)
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
    ^if.^if.^na<$ -,
    ^if.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg1_data a b, ca)] <- witness;
    }
  ]

  proc send_msg2 [
    ^if.^match#Some.^if.^nb<$ -,
    ^if.^match#Some.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg2_data a b ca, cb)] <- witness;
    }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^ok<$ -,
    ^if.^match#IPending.^match#Some.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg3_data a b ca m2, caf)] <- witness;
    },
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ { 
      (na, ok) <$ dnonce `*` dnonce;
      prfkey_map.[(msg3_data a b ca m2, caf)] <- (na, ok);
      skey <- prf (na, ok) (a, b);
    } 
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- prf (oget prfkey_map.[(msg3_data a b ca cb, m3)]) (a, b);
    }
  ]
}.

module Game6 = Game5 with {
  var cache : ((msg_data * ctxt) * (id * id), skey) fmap
  
  proc init_mem [
    -1 + { cache <- empty; }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ {
       skey <$ dskey;
       if (((msg3_data a b ca m2, caf), (a, b)) \notin cache) 
         cache.[((msg3_data a b ca m2, caf), (a, b))] <- skey;
    }
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- oget cache.[((msg3_data a b ca cb, m3), (a, b))];
    }
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
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
auto => /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (GWAKE0_observed _ _ _ _ role{m} trace{m} k).
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
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
auto => /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (GWAKE0_observed _ _ _ _ role{m} trace{m} k).
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
sp; if => //.
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
sp; if => //.
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
sp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => /> &m decn st inv abin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv aiin n _ ca0 cin a' i'.
case ((a', i') = (a, i){m}) => [<-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game1_inv_send_fin: Game1.send_fin:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
- auto => /> &m decn st inv bjin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [<-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
exact /Game1_inv_neq/inv.
qed.

hoare Game1_inv_rev_skey: Game1.rev_skey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game1_inv_test: Game1.test:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
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
+ exact Game1_undef.
+ exact (Game1_aborted _ _ _ _ r).
+ apply (Game1_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite mem_set pskcb.
+ apply (Game1_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  by rewrite mem_set pskcb.
+ exact (Game1_accepted _ _ _ _ r tr k).
exact (Game1_observed _ _ _ _ r tr k).
qed.
    
hoare Game2_inv_send_msg1: Game2.send_msg1:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
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
sp; if => //.
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
sp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => /> &m decn st inv abin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv aiin ca0 _ n cin a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a', b{m}))).
  by rewrite get_set_sameE. 
exact /Game1_inv_neq/inv.
qed.

hoare Game2_inv_send_fin: Game2.send_fin:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
- auto => /> &m decn st inv bjin a' i'.
  exact /Game1_inv_aborted/inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [[] <<- <-|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, a'))).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game2_inv_rev_skey: Game2.rev_skey:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
qed.

hoare Game2_inv_test: Game2.test:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [[] <<- <-|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE.
exact /Game1_inv_neq/inv.
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
if => //.
by auto.
qed.
    
hoare Game3_inv_send_msg1: Game3.send_msg1:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
seq 1 : (#pre); 1: by auto.
case (Game3.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto => /> &m _ inv ainin abin _ uniq na _ a' i'.
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
sp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  exact /Game3_inv_aborted/inv.
seq 1 : (#pre); 1: by auto.
case (Game3.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto => /> &m _ decn st inv bjnin abin _ bad n _ a' i'.
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
sp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => /> &m decn st inv abin a' i'.
  exact /Game3_inv_aborted/inv.
seq 1 : (#pre); 1: by auto.
case (Game3.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto => /> &m _ decn st inv aiin _ bad ok _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (Game3_accepted _ _ _ _ Initiator (m1{m}, m2{m}, caf{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
exact /Game3_inv_neq_sm/Game3_inv_neq_dm/inv.
qed.

hoare Game3_inv_send_fin: Game3.send_fin:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1: auto; 2..4: auto.
sp; match.
- auto => /> &m decn st inv bjin a' i'.
  exact /Game3_inv_aborted/inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ apply (Game3_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
exact /Game3_inv_neq_sm/inv.
qed.

hoare Game3_inv_rev_skey: Game3.rev_skey:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE. 
exact /Game3_inv_neq_sm/inv.
qed.

hoare Game3_inv_test: Game3.test:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} k).
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
sp; if=> //.
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
  smt().
exact /Game5_inv_neq_sm/Game5_inv_neq_dm/inv5.
qed.

hoare Game5_inv_send_msg2: Game5.send_msg2:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; if=> //.
sp; match => //.
+ auto=> />.
  move=> &m dm sm inv1 inv2 inv3 inv4 inv5 bjnin abin.
  split; 1: smt(get_setE).
  move=> b j.
  exact /Game5_inv_aborted/inv5.
seq 1 : (#pre); 1: by auto.
case (Game5.bad).
+ by rcondf ^if; auto=> />.
auto=> />.
move=> &m dm sm inv1 inv2 inv3 inv4 inv5 bjnin abin _ cbnin.
split; 1: smt(get_setE).
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
sp; if=> //.
sp; match => //.
sp; match => //.
+ auto=> />.
  move=> &m dm sm inv1 inv2 inv3 inv4 inv5 aiin.
  split; 1: smt(get_setE).
  move=> a i.
  exact /Game5_inv_aborted/inv5.
seq 1 : (#pre); 1: by auto.
case (Game5.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto=> />.
move=> &m _ dm sm inv1 inv2 inv3 inv4 inv5 /domE aiin _ cafnin ns _.
split; 1: smt(get_setE).
move=> a' i'.
case: ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_accepted _ _ _ _ _ Initiator (m1, m2, caf){m} (prf (ns.`1, ns.`2) (a, b)){!m}).
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
sp; if=> //.
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
- apply (Game5_accepted _ _ _ _ _ Responder (m1, m2, m3){m} (prf (oget Game5.prfkey_map{m}.[(msg3_data a{m} b{m} ca{m} cb{m}, m3{m})]) (a, b)){m}).
  by rewrite get_set_sameE. 
exact /Game5_inv_neq_sm/inv5. 
qed.

hoare Game5_inv_rev_skey: Game5.rev_skey:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; if=> //.
sp; match => //; 2: by auto.
sp; if=> //.
wp 2.
conseq (: _ ==> true); last by auto.
auto => /> &m st inv1 inv2 inv3 inv4 inv5 aiin _ k.
split; 1: smt(get_setE).
move=> a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_observed _ _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE.
exact /Game5_inv_neq_sm/inv5. 
qed.

hoare Game5_inv_test: Game5.test:
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map)
  ==>
  (Game5_inv_full Game5.state_map Game5.dec_map Game5.prfkey_map).
proof.
proc.
sp; if=> //.
sp; match => //; 2: by auto.
sp; if=> //.
wp 2.
conseq (: _ ==> true); last by auto.
auto => /> &m st inv1 inv2 inv3 inv4 inv5 aiin _ k.
split; 1: smt(get_setE).
move=> a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_observed _ _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE.
exact /Game5_inv_neq_sm/inv5. 
qed.
