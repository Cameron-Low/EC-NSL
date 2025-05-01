require import AllCore FMap FSet Distr NSL List.
import GWAKEc AEADc.

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
        ps <- get_partners (a, i) (Some trace) role state_map;
        if (card ps <= 1) {
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
  proc rev_skey [
    ^if.^match#Accepted.^if.^if.^k<- ~ {
      k <- oget sk_map.[trace];
    } 
  ]
  proc test [
    ^if.^match#Accepted.^if.^if.^if.^k<- ~ {
      k <- oget sk_map.[trace];
    } 
  ]
}.

module Game8 = Game7 with {
  proc send_msg3 [
    [^if.^match#IPending.^match#Some.^if.^skey<$ - ^sk_map<-] -
  ]

  proc rev_skey [
    var k'' : skey

    ^if.^match#Accepted.^if.^if.^k<- ~ {
      k'' <$ dskey;
      if (trace \notin sk_map) {
        sk_map.[trace] <- k'';
      }
      k <- oget Game8.sk_map.[trace];
    }
  ]

  proc test [
    var k'' : skey

    ^if.^match#Accepted.^if.^if.^if ~ {
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
(* Game 8 invariants *)

print Game8.

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
  & ((b, j) <> (a, i))
| Game8_accepted_r b j st c1 c2 c3 of
    (sm.[a, i] = Some (Responder, Accepted ((b, c1), c2, c3) witness))
  & (((b, a), msg3_data b a c1 c2, c3) \in dm)
  & (sm.[b, j] = Some (Initiator, st))
  & (c1 \in get_msgs st /\ c2 \in get_msgs st /\ c3 \in get_msgs st)
  & (!is_observed st => ((b, c1), c2, c3) \notin skm)
  & ((b, j) <> (a, i))
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
  & (forall a b c1 c2, ((a, b), msg2_data a b c1, c2) \in dm => c <> c1 /\ c <> c2)
  & (forall a b c1 c2 c3, ((a, b), msg3_data a b c1 c2, c3) \in dm => c <> c1 /\ c <> c2 /\ c <> c3)
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
  + by rewrite mem_set; right.
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
  + smt().
  move : smbj.
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
      rewrite smbj => /> smbj' dmc3 nsk ? ? ? ?.
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
  + case (inv1 a{m} i); rewrite smai //.
    + smt(get_setE).
    + smt(get_setE).
    case (inv2 cb{m}); smt().
  move : smai => /#.

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
    rewrite smbj => /> smbj' dmc3 nsk ? ? ? ?.
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

hoare Game8_inv_rev_skey: Game8.rev_skey:
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map
  ==>
  Game8_inv_full Game8.state_map Game8.dec_map Game8.sk_map.
proof.
proc.
sp; wp ^if; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //; sp; if => //.
rcondt ^if.
+ auto => /> &m st inv1 inv2 inv3 inv4 aiin card_ps card_obs_ps sk _.
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
    have bj_partner : (b, j) \in get_partners (a, i){m} (Some ((a{m}, c1), c2, c3)) Initiator Game8.state_map{m}.
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
  have bj_partner : (b, j) \in get_partners (a, i){m} (Some ((b, c1), c2, c3)) Responder Game8.state_map{m}.
  + rewrite /get_partners mem_fdom mem_filter /#.
  have // : (b, j) \in get_observed_partners (a, i){m} Game8.state_map{m}.
  + rewrite /get_observed_partners in_filter /#.
  rewrite fcard_eq0 in card_obs_ps.
  by rewrite card_obs_ps in_fset0.
 
auto => /> &m st inv1 inv2 inv3 inv4 aiin card_ps card_obs_ps sk _. 
rewrite get_set_sameE //=.

case: (role{m} = Initiator) => [->> | neqInit].
have smai : Game8.state_map.[a, i]{m} = Some (Initiator, Accepted trace{m} k'{m}) by smt().
case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stb c1 c2 c3 !->> dmc3 nskm smbj c1_in_stb c2_in_stb c3_in_stb neqbj.
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
+ move => b' j' stb' c1' c2' c3' sma' dmc3' smbj' c_in_stb' c3'_tr obs_sk neqbj'.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  + case (inv2 c3); smt(get_setE).
+ move => b'' j' stb' c1' c2' c3'.
  case ((b'', j') = (a, i){m}).
  + move => />.
    rewrite smai => /> smai' dmc3'.
    case (inv2 c3); 1..3: smt(get_setE).
    case (c3 = c3');2: smt(get_setE).
    move => />.
    have /> := inv3 _ _ _ _ _ dmc3 dmc3'.
    move => *.
    apply (Game8_accepted_r _ _ _ _ _ a{m} i{m} (Observed ((a{m}, c1'), c2', c3') sk) c1' c2' c3') => //.
    + smt(get_setE).
    by rewrite get_set_sameE.
  move => neqbj' sma' dmc3' smbj' c_in_stb obs_skmn neq.
  apply (Game8_accepted_r _ _ _ _ _ b'' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).  
  case (inv2 c3); smt(get_setE).
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

(**)
case: (role{m} = Responder) => [->> | /#].
have smai : Game8.state_map.[a, i]{m} = Some (Responder, Accepted trace{m} k'{m}) by smt().
case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stbj c1 c2 c3 !->> dmc3 smbj c1_in_stbj c2_in_stbj c3_in_stbj obs_skm neq. 
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
  move => neq' smai' dmc3' smbj' c_in_stb' c3'_tr obs_sk bj_neq_ai'.
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
+ move => b' j' stb c1' c2' c3' sma' dmc3' smbj' c_in_stb obs_sk neqbj.
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
sp; if => //; sp; if => //.
rcondt ^if.
+ auto => /> &m st inv1 inv2 inv3 inv4 aiin card_ps card_obs_ps sk _.
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
    have bj_partner : (b, j) \in get_partners (a, i){m} (Some ((a{m}, c1), c2, c3)) Initiator Game8.state_map{m}.
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
  have bj_partner : (b, j) \in get_partners (a, i){m} (Some ((b, c1), c2, c3)) Responder Game8.state_map{m}.
  + rewrite /get_partners mem_fdom mem_filter /#.
  have // : (b, j) \in get_observed_partners (a, i){m} Game8.state_map{m}.
  + rewrite /get_observed_partners in_filter /#.
  rewrite fcard_eq0 in card_obs_ps.
  by rewrite card_obs_ps in_fset0.

seq 1 : #pre; 1: by auto => />.
sp. 
seq 1 : #pre; 1: by auto => />.

auto => /> &m skm st inv1 inv2 inv3 inv4 aiin card_ps card_obs_ps. 

case: (role{m} = Initiator) => [->> | neqInit].
have smai : Game8.state_map.[a, i]{m} = Some (Initiator, Accepted trace{m} k'{m}) by smt().
case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stb c1 c2 c3 !->> dmc3 nskm smbj c1_in_stb c2_in_stb c3_in_stb neqbj.
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
+ move => b' j' stb' c1' c2' c3' sma' dmc3' smbj' c_in_stb' c3'_tr obs_sk neqbj'.
  apply (Game8_accepted_i _ _ _ _ _ b' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).
  + case (inv2 c3); smt(get_setE).
+ move => b'' j' stb' c1' c2' c3'.
  case ((b'', j') = (a, i){m}).
  + move => />.
    rewrite smai => /> smai' dmc3'.
    case (inv2 c3); 1..3: smt(get_setE).
    case (c3 = c3');2: smt(get_setE).
    move => />.
    have /> := inv3 _ _ _ _ _ dmc3 dmc3'.
    move => *.
    apply (Game8_accepted_r _ _ _ _ _ a{m} i{m} (Observed ((a{m}, c1'), c2', c3') k{m}) c1' c2' c3') => //.
    + smt(get_setE).
    by rewrite get_set_sameE.
  move => neqbj' sma' dmc3' smbj' c_in_stb obs_skmn neq.
  apply (Game8_accepted_r _ _ _ _ _ b'' j' stb' c1' c2' c3') => //.
  + by rewrite get_set_neqE.
  + smt(get_setE).  
  case (inv2 c3); smt(get_setE).
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

(**)
case: (role{m} = Responder) => [->> | /#].
have smai : Game8.state_map.[a, i]{m} = Some (Responder, Accepted trace{m} k'{m}) by smt().
case (inv1 a{m} i{m}); rewrite smai //=.
move => /> b j stbj c1 c2 c3 !->> dmc3 smbj c1_in_stbj c2_in_stbj c3_in_stbj obs_skm neq. 
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
  move => neq' smai' dmc3' smbj' c_in_stb' c3'_tr obs_sk bj_neq_ai'.
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
+ move => b' j' stb c1' c2' c3' sma' dmc3' smbj' c_in_stb obs_sk neqbj.
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
(* ------------------------------------------------------------------------------------------ *)
(* Game 0 invariants *)

inductive GWAKEb_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
| GWAKEb_undef of
    (sm.[a, i] = None)
| GWAKEb_aborted r st of
    (sm.[a, i] = Some (r, Aborted st))
| GWAKEb_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & (pskm.[a, b] = Some kab)
| GWAKEb_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & (pskm.[b, a] = Some kba)
| GWAKEb_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| GWAKEb_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma GWAKEb_inv_neq a i c j v sm psk:
! (c = a /\ j = i) =>
GWAKEb_inv sm psk c j =>
GWAKEb_inv sm.[(a, i) <- v] psk c j.
proof.
move=> neq
[
smbj
| r st smbj
| b na c1 kab smbj pskcb
| b na nb c1 c2 kba smbj pskcb
| r tr k smbj
| r tr k smbj
].
+ apply GWAKEb_undef.
  by rewrite get_set_neqE.
+ apply (GWAKEb_aborted _ _ _ _ r st).
  by rewrite get_set_neqE.
+ apply (GWAKEb_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ apply (GWAKEb_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ apply (GWAKEb_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
apply (GWAKEb_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

hoare GWAKEb_inv_gen_pskey: GWAKEb(NSL).gen_pskey:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
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
+ exact GWAKEb_undef.
+ exact (GWAKEb_aborted _ _ _ _ r).
+ apply (GWAKEb_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).  
+ apply (GWAKEb_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  smt(get_setE).
+ exact (GWAKEb_accepted _ _ _ _ r tr k).
exact (GWAKEb_observed _ _ _ _ r tr k).
qed.
    
lemma GWAKEb_inv_aborted a i b j r st sm pm: GWAKEb_inv sm pm a i => GWAKEb_inv sm.[(b, j) <- (r, Aborted st)] pm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (GWAKEb_aborted _ _ _ _ r st).
  by rewrite get_set_sameE.
exact /GWAKEb_inv_neq/inv.
qed.

hoare GWAKEb_inv_send_msg1: GWAKEb(NSL).send_msg1:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
proc; inline *.
sp; if => //.
auto => /> &m inv ainin /domE abin na _ ca _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (GWAKEb_ipending _ _ _ _ b{m} na ca (oget GWAKEb.psk_map.[(a, b)]{m})).
  - by rewrite get_set_sameE.
  exact some_oget.
exact /GWAKEb_inv_neq/inv.
qed.
    
hoare GWAKEb_inv_send_msg2: GWAKEb(NSL).send_msg2:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ match None ^match; 1: by auto.
  auto => /> &m decn st inv bjnin abin a' i'.
  exact /GWAKEb_inv_aborted/inv.
match Some ^match; 1: by auto=> /#.
auto => /> &m decn st inv bjnin /domE abin n _ cb0 cin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKEb_rpending _ _ _ _ a0{m} na{m} n ca{m} cb0 (oget GWAKEb.psk_map.[(a0, b)]{m})).
  - by rewrite get_set_sameE.
  exact some_oget.
exact /GWAKEb_inv_neq/inv.
qed.

hoare GWAKEb_inv_send_msg3: GWAKEb(NSL).send_msg3:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: by auto.
sp; match.
- match None ^match; 1: by auto.
  auto => /> &m decn st inv aiin a' i'.
  exact /GWAKEb_inv_aborted/inv.
match Some ^match; 1: auto => /#.
auto => /> &m decn st inv aiin n _ ca0 cin a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKEb_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
exact /GWAKEb_inv_neq/inv.
qed.

hoare GWAKEb_inv_send_fin: GWAKEb(NSL).send_fin:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1, 3..5: by auto.
sp; match.
- match None ^match; 1: by auto.
  auto => /> &m decn st inv bjin a' i'.
  exact /GWAKEb_inv_aborted/inv.
match Some ^match; 1: auto => /#.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKEb_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
exact /GWAKEb_inv_neq/inv.
qed.

hoare GWAKEb_inv_rev_skey: GWAKEb(NSL).rev_skey:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
auto => /> &m st inv aiin _ _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (GWAKEb_observed _ _ _ _ role{m} trace{m} k'{m}).
  by rewrite get_set_sameE.
exact /GWAKEb_inv_neq/inv.
qed.

hoare GWAKEb_inv_test: GWAKEb(NSL).test:
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKEb_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1,2,4,5: by auto.
sp; if => //; sp; if => //.
if => //.
+ auto => /> &m st inv aiin _ _ a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (GWAKEb_observed _ _ _ _ role{m} trace{m} k'{m}).
    by rewrite get_set_sameE.
  exact /GWAKEb_inv_neq/inv.
auto => /> &m st inv aiin _ _ ideal sk _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (GWAKEb_observed _ _ _ _ role{m} trace{m} sk).
  by rewrite get_set_sameE.
exact /GWAKEb_inv_neq/inv.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1 invariants *)

inductive Game1_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
| Game1_undef of
    (sm.[a, i] = None)
| Game1_aborted r st of
    (sm.[a, i] = Some (r, Aborted st))
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
| r st smbj
| b na c1 kab smbj pskcb
| b na nb c1 c2 kba smbj pskcb
| r tr k smbj
| r tr k smbj
].
+ apply Game1_undef.
  by rewrite get_set_neqE.
+ apply (Game1_aborted _ _ _ _ r st).
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

lemma Game1_inv_aborted a i b j r st sm pm: Game1_inv sm pm a i => Game1_inv sm.[(b, j) <- (r, Aborted st)] pm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (Game1_aborted _ _ _ _ r st).
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
sp; if => //; sp; if => //.
if => //.
+ auto => /> &m st inv aiin _ _ a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (Game1_observed _ _ _ _ role{m} trace{m} k'{m}).
    by rewrite get_set_sameE.
  exact /Game1_inv_neq/inv.
auto => /> &m st inv aiin _ _ ideal sk _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} sk).
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
have t: equiv[Game2.test ~ Game1.test: ={arg} /\ ={b0, state_map, psk_map}(Game2, Game1) ==> ={b0, state_map, psk_map}(Game2, Game1)] by sim />.
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
| Game3_aborted r st of
    (sm.[a, i] = Some (r, Aborted st))
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
| r st smbj
| b na c1 kab smbj dmcb
| b na nb c1 c2 kba smbj dmcb
| r tr k smbj
| r tr k smbj
].
+ apply Game3_undef.
  by rewrite get_set_neqE.
+ apply (Game3_aborted _ _ _ _ r st).
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
| r st smbj pk ad
| b na c1 kab smbj dmcb pk ad
| b na nb c1 c2 kba smbj dmnb dmna pk ad
| r tr k smbj pk ad
| r tr k smbj pk ad
].
+ exact Game3_undef.
+ exact (Game3_aborted _ _ _ _ r st).
+ apply (Game3_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).  
+ apply (Game3_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  + smt(get_setE).  
  smt(get_setE).  
+ exact (Game3_accepted _ _ _ _ r tr k).
exact (Game3_observed _ _ _ _ r tr k).
qed.

lemma Game3_inv_aborted a i b j r st sm dm: Game3_inv sm dm a i => Game3_inv sm.[(b, j) <- (r, Aborted st)] dm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (Game3_aborted _ _ _ _ r st).
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
sp; if => //; sp; if => //.
if => //.
+ auto => /> &m st inv aiin _ _ a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (Game3_observed _ _ _ _ role{m} trace{m} k'{m}).
    by rewrite get_set_sameE.
  exact /Game3_inv_neq_sm/inv.
auto => /> &m st inv aiin _ _ ideal sk _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} sk).
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
| Game5_aborted r st of
    (sm.[a, i] = Some (r, Aborted st))
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
| r st smbj
| b c1 smbj
| b c1 c2 smbj
| r tr k smbj
| r tr k smbj
].
+ apply Game5_undef.
  by rewrite get_set_neqE.
+ apply (Game5_aborted _ _ _ _ _ r st).
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
| r st smbj
| b c1 smbj v1 v2
| b c1 c2 smbj
| r tr k smbj
| r tr k smbj
] pk ad.
+ exact Game5_undef.
+ exact (Game5_aborted _ _ _ _ _ r st).
+ apply (Game5_ipending _ _ _ _ _ b c1) => //.
  by rewrite mem_set v1.  
+ exact (Game5_rpending _ _ _ _ _ b c1 c2).
+ exact (Game5_accepted _ _ _ _  _ r tr k).
exact (Game5_observed _ _ _ _ _ r tr k).
qed.

lemma Game5_inv_aborted a i b j r st sm dm nm: Game5_inv sm dm nm a i => Game5_inv sm.[(b, j) <- (r, Aborted st)] dm nm a i.
proof.
move=> inv.
case ((a, i) = (b, j)) => /> => [|neq_ai].
- apply (Game5_aborted _ _ _ _ _ r st).
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
sp; if => //; sp; if => //.
if => //.
+ auto => /> &m st inv1 inv2 inv3 inv4 inv5 aiin _ _.
  split; 1: smt(get_setE).
  move=> a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (Game5_observed _ _ _ _ _ role{m} trace{m} k'{m}).
    by rewrite get_set_sameE.
  exact /Game5_inv_neq_sm/inv5.
auto => /> &m st inv1 inv2 inv3 inv4 inv5 aiin _ _ ideal sk _.
split; 1: smt(get_setE).
move=> a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game5_observed _ _ _ _ _ role{m} trace{m} sk).
  by rewrite get_set_sameE.
exact /Game5_inv_neq_sm/inv5.
qed.
