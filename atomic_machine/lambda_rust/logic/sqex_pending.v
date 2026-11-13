(** Reservation accounting while different threads are between Try and Commit.
    A pending Free keeps a reservation-map tombstone after the value was freed. *)
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.sq_sem.
Require Import VST.atomic_machine.lambda_rust.equivalence.
From stdpp Require Import gmap list.

Set Default Proof Using "Type".

Inductive sqex_access_kind := SqexRead | SqexWrite | SqexFree.

Definition sqex_event_count (kind : sqex_access_kind) (l : loc) (ev : @mem_ev loc) : nat :=
  match ev, kind with
  | atomic_machine.Read k, SqexRead
  | atomic_machine.Write k, SqexWrite
  | atomic_machine.Free k, SqexFree => if decide (k = l) then 1%nat else 0%nat
  | _, _ => 0%nat
  end.

Definition sqex_trace_count kind l (T : list (@mem_ev loc)) : nat :=
  foldr (fun ev n => sqex_event_count kind l ev + n)%nat 0%nat T.

Lemma sqex_trace_count_app kind l T U :
  sqex_trace_count kind l (T ++ U) =
    (sqex_trace_count kind l T + sqex_trace_count kind l U)%nat.
Proof. unfold sqex_trace_count. induction T as [|ev T IH]; simpl; lia. Qed.

Global Instance sqex_trace_count_permutation kind l :
  Proper ((≡ₚ) ==> eq) (sqex_trace_count kind l).
Proof.
  intros T U Hperm. unfold sqex_trace_count. induction Hperm; simpl; try done; lia.
Qed.

Inductive sqex_reservation_cell : option val -> nat -> nat -> nat -> option rw_state -> Prop :=
| SqexAbsent : sqex_reservation_cell None 0 0 0 None
| SqexReaders v n : sqex_reservation_cell (Some v) n 0 0 (Some (Rst n))
| SqexWriter v : sqex_reservation_cell (Some v) 0 1 0 (Some Wst)
| SqexFreed : sqex_reservation_cell None 0 0 1 (Some (Rst 0)).

Definition sqex_reservations (m : lr_mem) (T : list (@mem_ev loc)) (mu : rw_map) : Prop :=
  forall l, sqex_reservation_cell (m !! l)
    (sqex_trace_count SqexRead l T) (sqex_trace_count SqexWrite l T)
    (sqex_trace_count SqexFree l T) (mu !! l).

Lemma sqex_reservations_nil m :
  sqex_reservations m [] ((fun _ => Rst 0) <$> m).
Proof.
  intros l. rewrite lookup_fmap. destruct (m !! l) eqn:Hl; rewrite Hl /=; constructor.
Qed.

Global Instance sqex_reservations_permutation m :
  Proper ((≡ₚ) ==> eq ==> iff) (sqex_reservations m).
Proof.
  intros T U Hperm mu mu' ->. unfold sqex_reservations.
  by setoid_rewrite Hperm.
Qed.

Lemma sqex_reservations_cons_commute m ev T U mu :
  sqex_reservations m (ev :: T ++ U) mu <->
  sqex_reservations m (T ++ ev :: U) mu.
Proof.
  apply sqex_reservations_permutation; last done.
  apply Permutation_middle.
Qed.

Lemma sqex_cell_fin_read ov r w f st :
  sqex_reservation_cell ov (S r) w f st ->
  st = Some (Rst (S r)) /\ sqex_reservation_cell ov r w f (Some (Rst r)).
Proof. intros H; inversion H; subst. split; first done. constructor. Qed.

Lemma sqex_cell_fin_write ov r w f st :
  sqex_reservation_cell ov r (S w) f st ->
  st = Some Wst /\ sqex_reservation_cell ov r w f (Some (Rst 0)).
Proof. intros H; inversion H; subst. split; first done. constructor. Qed.

Lemma sqex_cell_fin_free ov r w f st :
  sqex_reservation_cell ov r w (S f) st ->
  st = Some (Rst 0) /\ sqex_reservation_cell ov r w f None.
Proof. intros H; inversion H; subst. split; first done. constructor. Qed.

Lemma sqex_reservations_fin_event m (ev : @mem_ev loc) T mu :
  sqex_reservations m (ev :: T) mu ->
  exists mu', fin_ev ev (Some mu) = Some mu' /\ sqex_reservations m T mu'.
Proof.
  intros Hres. destruct ev as [l|l|l|l].
  - have Hl := Hres l.
    rewrite /sqex_trace_count /sqex_event_count /= decide_True in Hl; last done.
    apply sqex_cell_fin_read in Hl as [Hmu Hnext].
    exists (<[l := Rst (sqex_trace_count SqexRead l T)]> mu). split.
    + unfold fin_ev, fin_Read. simpl.
      by rewrite Hmu.
    + intros k. destruct (decide (l = k)) as [<-|Hne].
      * rewrite lookup_insert_eq. exact Hnext.
      * rewrite lookup_insert_ne; last done.
        specialize (Hres k). rewrite /sqex_trace_count /sqex_event_count /= decide_False in Hres; last done.
        exact Hres.
  - have Hl := Hres l.
    rewrite /sqex_trace_count /sqex_event_count /= decide_True in Hl; last done.
    apply sqex_cell_fin_write in Hl as [Hmu Hnext].
    exists (<[l := Rst 0]> mu). split.
    + unfold fin_ev, fin_Write. simpl.
      by rewrite Hmu.
    + intros k. destruct (decide (l = k)) as [<-|Hne].
      * rewrite lookup_insert_eq. exact Hnext.
      * rewrite lookup_insert_ne; last done.
        specialize (Hres k). rewrite /sqex_trace_count /sqex_event_count /= decide_False in Hres; last done.
        exact Hres.
  - exists mu. split; first done. exact Hres.
  - have Hl := Hres l.
    rewrite /sqex_trace_count /sqex_event_count /= decide_True in Hl; last done.
    apply sqex_cell_fin_free in Hl as [Hmu Hnext].
    exists (delete l mu). split.
    + unfold fin_ev, fin_Free. simpl.
      by rewrite Hmu.
    + intros k. destruct (decide (l = k)) as [<-|Hne].
      * rewrite lookup_delete_eq. exact Hnext.
      * rewrite lookup_delete_ne; last done.
        specialize (Hres k). rewrite /sqex_trace_count /sqex_event_count /= decide_False in Hres; last done.
        exact Hres.
Qed.

Lemma sqex_reservations_fin m T D mu :
  sqex_reservations m (T ++ D) mu ->
  exists mu', atomic_machine.fin T mu = Some mu' /\ sqex_reservations m D mu'.
Proof.
  revert D mu. induction T as [|ev T IH]; intros D mu Hres.
  - exists mu. done.
  - apply sqex_reservations_cons_commute in Hres.
    destruct (IH (ev :: D) mu Hres) as (mu1 & Hfin & Hres1).
    destruct (sqex_reservations_fin_event _ _ _ _ Hres1) as (mu2 & Hev & Hres2).
    exists mu2. split; last done.
    change (fin_ev ev (atomic_machine.fin T mu) = Some mu2). by rewrite Hfin.
Qed.

Definition sqex_pending_trace (t : tstate) : list (@mem_ev loc) :=
  match t with Running _ T => T | StuckState => [] end.

Definition sqex_pending_events (tp : tpool) : list (@mem_ev loc) :=
  mjoin ((fun it => sqex_pending_trace it.2) <$> map_to_list tp).

Lemma sqex_pending_events_delete tp i e T :
  tp !! i = Some (Running e T) ->
  sqex_pending_events tp ≡ₚ T ++ sqex_pending_events (delete i tp).
Proof.
  intros Hi. unfold sqex_pending_events.
  rewrite <- (map_to_list_delete tp i (Running e T) Hi). done.
Qed.

Lemma sqex_pending_events_insert tp i e T :
  sqex_pending_events (<[i := Running e T]> tp) ≡ₚ
    T ++ sqex_pending_events (delete i tp).
Proof.
  rewrite (sqex_pending_events_delete _ i e T (lookup_insert_eq _ _ _)).
  by rewrite delete_insert_eq.
Qed.

Definition sqex_pool_reservations tp m mu : Prop :=
  sqex_reservations m (sqex_pending_events tp) mu.

Lemma sqex_pool_reservations_commit tp m mu i e T :
  sqex_pool_reservations tp m mu -> tp !! i = Some (Running e T) ->
  exists mu', atomic_machine.fin T mu = Some mu' /\
    sqex_pool_reservations (<[i := Running e []]> tp) m mu'.
Proof.
  intros Hres Hi. unfold sqex_pool_reservations in *.
  rewrite (sqex_pending_events_delete _ _ _ _ Hi) in Hres.
  destruct (sqex_reservations_fin _ _ _ _ Hres) as (mu' & Hfin & Hres').
  exists mu'. split; first done.
  by rewrite sqex_pending_events_insert /=.
Qed.

Lemma sqex_cell_reserve_read ov r w f n :
  sqex_reservation_cell ov r w f (Some (Rst n)) -> is_Some ov ->
  sqex_reservation_cell ov (S r) w f (Some (Rst (S n))).
Proof. intros H [v Hv]. inversion H; subst; simplify_eq; constructor. Qed.

Lemma sqex_cell_reserve_write ov r w f :
  sqex_reservation_cell ov r w f (Some (Rst 0)) -> is_Some ov ->
  sqex_reservation_cell ov r (S w) f (Some Wst).
Proof. intros H [v Hv]. inversion H; subst; simplify_eq; constructor. Qed.

Lemma sqex_cell_reserve_free ov r w f :
  sqex_reservation_cell ov r w f (Some (Rst 0)) -> is_Some ov ->
  sqex_reservation_cell None r w (S f) (Some (Rst 0)).
Proof. intros H [v Hv]. inversion H; subst; simplify_eq; constructor. Qed.

Lemma sqex_cell_allocate ov r w f v :
  sqex_reservation_cell ov r w f None ->
  sqex_reservation_cell (Some v) r w f (Some (Rst 0)).
Proof. inversion 1; subst. constructor. Qed.

Lemma sqex_reservations_read m D mu l n :
  sqex_reservations m D mu -> is_Some (m !! l) -> mu !! l = Some (Rst n) ->
  sqex_reservations m (lr_read_event l :: D) (<[l := Rst (S n)]> mu).
Proof.
  intros Hres Hm Hmu k. specialize (Hres k).
  destruct (decide (l = k)) as [<-|Hne].
  - rewrite lookup_insert_eq /sqex_trace_count /sqex_event_count /lr_read_event /= decide_True; last done.
    rewrite Hmu in Hres. by apply sqex_cell_reserve_read.
  - rewrite lookup_insert_ne; last done.
    rewrite /sqex_trace_count /sqex_event_count /lr_read_event /= decide_False; last done.
    exact Hres.
Qed.

Lemma sqex_cell_store ov r w f st v :
  is_Some ov -> sqex_reservation_cell ov r w f st ->
  sqex_reservation_cell (Some v) r w f st.
Proof. intros [old Hold] H. inversion H; subst; simplify_eq; constructor. Qed.

Lemma sqex_reservations_write m D mu l v :
  sqex_reservations m D mu -> is_Some (m !! l) -> mu !! l = Some (Rst 0) ->
  sqex_reservations (<[l := v]> m) (lr_write_event l :: D) (<[l := Wst]> mu).
Proof.
  intros Hres Hm Hmu k. specialize (Hres k).
  destruct (decide (l = k)) as [<-|Hne].
  - rewrite !lookup_insert_eq /sqex_trace_count /sqex_event_count /lr_write_event /= decide_True; last done.
    rewrite Hmu in Hres. apply sqex_cell_reserve_write in Hres; last done.
    eapply sqex_cell_store; eauto.
  - rewrite !lookup_insert_ne; try done.
    rewrite /sqex_trace_count /sqex_event_count /lr_write_event /= decide_False; last done.
    exact Hres.
Qed.

Lemma sqex_reservations_free m D mu l :
  sqex_reservations m D mu -> is_Some (m !! l) -> mu !! l = Some (Rst 0) ->
  sqex_reservations (delete l m) (lr_free_event l :: D) mu.
Proof.
  intros Hres Hm Hmu k. specialize (Hres k).
  destruct (decide (l = k)) as [<-|Hne].
  - rewrite lookup_delete_eq Hmu /sqex_trace_count /sqex_event_count /lr_free_event /= decide_True; last done.
    rewrite Hmu in Hres. eapply sqex_cell_reserve_free; eauto.
  - rewrite lookup_delete_ne; last done.
    rewrite /sqex_trace_count /sqex_event_count /lr_free_event /= decide_False; last done.
    exact Hres.
Qed.

Lemma sqex_reservations_allocate m D mu l v :
  sqex_reservations m D mu -> mu !! l = None ->
  sqex_reservations (<[l := v]> m) D (<[l := Rst 0]> mu).
Proof.
  intros Hres Hmu k. specialize (Hres k).
  destruct (decide (l = k)) as [<-|Hne].
  - rewrite !lookup_insert_eq. rewrite Hmu in Hres. eapply sqex_cell_allocate; exact Hres.
  - by rewrite !lookup_insert_ne.
Qed.

Definition sqex_access_event kind l : @mem_ev loc :=
  match kind with SqexRead => lr_read_event l | SqexWrite => lr_write_event l
    | SqexFree => lr_free_event l end.

Lemma sqex_event_count_pos kind l ev :
  (0 < sqex_event_count kind l ev)%nat <-> ev = sqex_access_event kind l.
Proof.
  destruct kind, ev; simpl; try (split; [lia | discriminate]);
    case_decide; unfold sqex_access_event, lr_read_event, lr_write_event, lr_free_event;
    naive_solver lia.
Qed.

Lemma sqex_trace_count_pos kind l T :
  (0 < sqex_trace_count kind l T)%nat <-> sqex_access_event kind l ∈ T.
Proof.
  induction T as [|ev T IH].
  - simpl. split; [lia | inversion 1].
  - change ((0 < sqex_event_count kind l ev + sqex_trace_count kind l T)%nat <-> sqex_access_event kind l ∈ ev :: T).
    rewrite elem_of_cons. rewrite <-IH.
    have He := sqex_event_count_pos kind l ev.
    split.
    + intros H. destruct (decide (0 < sqex_event_count kind l ev)%nat) as [Hp|Hnp].
      * left. symmetry. by apply He.
      * right. lia.
    + intros [Heq|Hp]; last lia.
      have Hp : (0 < sqex_event_count kind l ev)%nat by apply He; symmetry; exact Heq.
      lia.
Qed.

Lemma sqex_trace_count_zero kind l T :
  sqex_trace_count kind l T = 0%nat <-> sqex_access_event kind l ∉ T.
Proof.
  split.
  - intros Hz Hin. apply sqex_trace_count_pos in Hin. lia.
  - intros Hnot. destruct (sqex_trace_count kind l T) eqn:Hcount; first done.
    exfalso. apply Hnot, sqex_trace_count_pos. lia.
Qed.

Lemma sqex_pending_events_elem tp ev :
  ev ∈ sqex_pending_events tp <->
  exists i e T, tp !! i = Some (Running e T) /\ ev ∈ T.
Proof.
  unfold sqex_pending_events. rewrite list_elem_of_join.
  split.
  - intros (T & Hev & HT). apply list_elem_of_fmap in HT as ([i t] & Heq & Hi). subst T.
    apply (elem_of_map_to_list (M := gmap nat)) in Hi. destruct t as [e T|]; simpl in Hev; last inversion Hev.
    by exists i, e, T.
  - intros (i & e & T & Hi & Hev). exists T. split; first done.
    apply list_elem_of_fmap. exists (i, Running e T). split; first done.
    by apply (elem_of_map_to_list (M := gmap nat)).
Qed.

Lemma sqex_trace_count_alloc kind k l n :
  sqex_trace_count kind k (lr_alloc_events l n) = 0%nat.
Proof.
  revert l. induction n as [|n IH]; intros l; first done.
  change ((sqex_event_count kind k (lr_alloc_event l) +
    sqex_trace_count kind k (lr_alloc_events (l +ₗ 1) n))%nat = 0%nat).
  rewrite IH. by destruct kind.
Qed.

Lemma sqex_reservations_alloc_events m D mu l n mu' :
  sqex_reservations m D mu -> rsv (lr_alloc_events l n) mu = Some mu' ->
  sqex_reservations (alloc_gmap (LitV LitPoison) l n m)
    (lr_alloc_events l n ++ D) mu'.
Proof.
  intros Hres. revert l mu'. induction n as [|n IH]; intros l mu' Hrsv.
  - simpl in Hrsv. injection Hrsv as <-. exact Hres.
  - change (rsv_ev (lr_alloc_event l) (rsv (lr_alloc_events (l +ₗ 1) n) mu) = Some mu') in Hrsv.
    destruct (rsv (lr_alloc_events (l +ₗ 1) n) mu) as [mu1|] eqn:Htail; last discriminate.
    specialize (IH _ _ Htail).
    change (rsv_Alloc mu1 l = Some mu') in Hrsv.
    unfold rsv_Alloc in Hrsv. destruct (mu1 !! l) eqn:Hl; first discriminate.
    injection Hrsv as <-.
    have Halloc := sqex_reservations_allocate _ _ _ _ (LitV LitPoison) IH Hl.
    intros k. specialize (Halloc k). unfold sqex_reservations in IH.
    rewrite !sqex_trace_count_app !sqex_trace_count_alloc /= in Halloc |- *.
    exact Halloc.
Qed.

Lemma sqex_locs_member_range l n k :
  k ∈ lr_locs l n -> exists z, (0 <= z < Z.of_nat n)%Z /\ k = (l +ₗ z)%L.
Proof.
  revert l. induction n as [|n IH]; intros l Hk; first inversion Hk.
  apply elem_of_cons in Hk as [->|Hk].
  - exists 0%Z. split; first lia. by rewrite shift_loc_0.
  - destruct (IH _ Hk) as (z & Hz & ->).
    exists (1 + z)%Z. split; first lia. by rewrite shift_loc_assoc.
Qed.

Lemma sqex_locs_nodup l n : NoDup (lr_locs l n).
Proof.
  revert l. induction n as [|n IH]; intros l; first constructor.
  simpl. constructor; last apply IH.
  intros Hin. destruct (sqex_locs_member_range _ _ _ Hin) as (z & Hz & Heq).
  destruct l as [b o]. unfold shift_loc in Heq. simpl in Heq. injection Heq. lia.
Qed.

Fixpoint sqex_delete_locs (ls : list loc) (m : lr_mem) : lr_mem :=
  match ls with [] => m | l :: ls => delete l (sqex_delete_locs ls m) end.

Lemma sqex_delete_locs_lookup m ls l :
  l ∉ ls -> sqex_delete_locs ls m !! l = m !! l.
Proof.
  induction ls as [|k ls IH]; intros Hnot; first done.
  apply not_elem_of_cons in Hnot as [Hne Hnot]. simpl.
  rewrite lookup_delete_ne; [by apply IH | congruence].
Qed.

Lemma sqex_delete_locs_free m l n :
  sqex_delete_locs (lr_locs l n) m = free_gmap l n m.
Proof. revert l. induction n as [|n IH]; intros l; simpl; [done | by rewrite IH]. Qed.

Lemma sqex_reservations_free_locs m D mu ls :
  NoDup ls -> sqex_reservations m D mu ->
  (forall l, l ∈ ls -> is_Some (m !! l) /\ mu !! l = Some (Rst 0)) ->
  sqex_reservations (sqex_delete_locs ls m) ((lr_free_event <$> ls) ++ D) mu.
Proof.
  intros Hnodup Hres Hfree. induction Hnodup as [|l ls Hnot Hnodup IH]; first done.
  have Htail : forall k, k ∈ ls -> is_Some (m !! k) /\ mu !! k = Some (Rst 0).
  { intros k Hk. apply Hfree. by right. }
  specialize (IH Htail). destruct (Hfree l ltac:(by left)) as [Hm Hmu].
  simpl. apply sqex_reservations_free; [exact IH | | exact Hmu].
  by rewrite sqex_delete_locs_lookup.
Qed.

Lemma sqex_reservations_try m D mu T m' mu' :
  sqex_reservations m D mu -> lr_mem_effect m T m' ->
  (forall l, lr_free_event l ∈ T -> mu !! l = Some (Rst 0)) ->
  rsv T mu = Some mu' -> sqex_reservations m' (T ++ D) mu'.
Proof.
  intros Hres Heffect Hfree Hrsv. destruct Heffect.
  - simpl in Hrsv. by injection Hrsv as <-.
  - change (rsv_Read mu l = Some mu') in Hrsv. unfold rsv_Read in Hrsv.
    destruct (mu !! l) as [[n|]|] eqn:Hmu; try rewrite Hmu in Hrsv; simpl in Hrsv; try discriminate.
    injection Hrsv as <-. by apply sqex_reservations_read.
  - change (rsv_Write mu l = Some mu') in Hrsv. unfold rsv_Write in Hrsv.
    destruct (mu !! l) as [[n|]|] eqn:Hmu; try rewrite Hmu in Hrsv; simpl in Hrsv; try discriminate.
    destruct n; last discriminate. injection Hrsv as <-.
    by apply sqex_reservations_write.
  - eapply sqex_reservations_alloc_events; eauto.
  - rewrite lr_rsv_free_events in Hrsv. injection Hrsv as <-.
    rewrite <-sqex_delete_locs_free. apply sqex_reservations_free_locs.
    + apply sqex_locs_nodup.
    + exact Hres.
    + intros k Hk. split.
      * destruct (sqex_locs_member_range _ _ _ Hk) as (z & Hz & ->). by apply H.
      * apply Hfree. by apply list_elem_of_fmap_2.
Qed.

Lemma sqex_pool_reservations_try tp m mu i e T e' m' mu' :
  sqex_pool_reservations tp m mu -> tp !! i = Some (Running e []) ->
  lr_step e m T e' m' ->
  (forall l, lr_free_event l ∈ T -> mu !! l = Some (Rst 0)) ->
  rsv T mu = Some mu' ->
  sqex_pool_reservations (<[i := Running e' T]> tp) m' mu'.
Proof.
  intros Hres Hi Hstep Hfree Hrsv. unfold sqex_pool_reservations in *.
  rewrite (sqex_pending_events_delete _ _ _ _ Hi) /= in Hres.
  rewrite sqex_pending_events_insert.
  eapply sqex_reservations_try; eauto using lr_step_mem_effect.
Qed.

Lemma sqex_pool_reservations_ready_update tp m mu i e e' :
  sqex_pool_reservations tp m mu -> tp !! i = Some (Running e []) ->
  sqex_pool_reservations (<[i := Running e' []]> tp) m mu.
Proof.
  intros Hres Hi. unfold sqex_pool_reservations in *.
  rewrite (sqex_pending_events_delete _ _ _ _ Hi) /= in Hres.
  by rewrite sqex_pending_events_insert /=.
Qed.

Lemma sqex_pool_reservations_spawn tp m mu i e :
  sqex_pool_reservations tp m mu -> tp !! i = None ->
  sqex_pool_reservations (<[i := Running e []]> tp) m mu.
Proof.
  intros Hres Hi. unfold sqex_pool_reservations in *.
  by rewrite sqex_pending_events_insert (delete_id _ _ Hi).
Qed.

Lemma sqex_reservations_store m D mu l v :
  sqex_reservations m D mu -> is_Some (m !! l) ->
  sqex_reservations (<[l := v]> m) D mu.
Proof.
  intros Hres Hm k. destruct (decide (l = k)) as [<-|Hne].
  - rewrite lookup_insert_eq. eapply sqex_cell_store; eauto.
  - rewrite lookup_insert_ne; [apply Hres | done].
Qed.

Lemma sqex_pool_reservations_store tp m mu l v :
  sqex_pool_reservations tp m mu -> is_Some (m !! l) ->
  sqex_pool_reservations tp (<[l := v]> m) mu.
Proof. apply sqex_reservations_store. Qed.

Lemma sqex_pending_events_empty tp :
  (forall i t, tp !! i = Some t -> sqex_pending_trace t = []) ->
  sqex_pending_events tp = [].
Proof.
  intros Hempty. unfold sqex_pending_events. apply join_nil.
  apply Forall_fmap, Forall_forall. intros [i t] Hi.
  apply Hempty with i. by apply (elem_of_map_to_list (M := gmap nat)).
Qed.

Lemma sqex_pool_reservations_init tp m :
  (forall i t, tp !! i = Some t -> sqex_pending_trace t = []) ->
  sqex_pool_reservations tp m ((fun _ => Rst 0) <$> m).
Proof.
  intros Hempty. unfold sqex_pool_reservations.
  rewrite (sqex_pending_events_empty _ Hempty). apply sqex_reservations_nil.
Qed.

Lemma sqex_pool_reservations_pending_safe tp m mu i e T :
  sqex_pool_reservations tp m mu -> tp !! i = Some (Running e T) -> T ≠ [] ->
  am_not_stuck (Running e T) m mu.
Proof.
  intros Hres Hi Hne. apply am_pending_not_stuck; first done.
  destruct (sqex_pool_reservations_commit _ _ _ _ _ _ Hres Hi) as (mu' & Hfin & _).
  by exists mu'.
Qed.

Lemma sqex_cell_domain ov r w f st :
  sqex_reservation_cell ov r w f st ->
  (is_Some st <-> is_Some ov \/ (0 < f)%nat).
Proof.
  destruct 1.
  - split.
    + intros [x Hx]. discriminate.
    + intros [[x Hx]|H]; [discriminate | lia].
  - split; intros _; [left; by eexists | by eexists].
  - split; intros _; [left; by eexists | by eexists].
  - split; intros _; [right; lia | by eexists].
Qed.

Lemma sqex_cell_nil ov st :
  sqex_reservation_cell ov 0 0 0 st -> st = (fun _ => Rst 0) <$> ov.
Proof. inversion 1; subst; done. Qed.

(** Pending Free is exactly the exception to equality of allocated domains. *)
Lemma sqex_reservations_domain m D mu l :
  sqex_reservations m D mu ->
  (is_Some (mu !! l) <-> is_Some (m !! l) \/ lr_free_event l ∈ D).
Proof.
  intros Hres. specialize (Hres l).
  change (is_Some (mu !! l) <-> is_Some (m !! l) \/ sqex_access_event SqexFree l ∈ D).
  rewrite <-sqex_trace_count_pos. exact (sqex_cell_domain _ _ _ _ _ Hres).
Qed.

(** At an empty pending boundary, the maps agree and every cell is unreserved. *)
Lemma sqex_reservations_nil_eq m mu :
  sqex_reservations m [] mu -> mu = (fun _ => Rst 0) <$> m.
Proof.
  intros Hres. apply (map_eq (M := gmap loc)). intros l. rewrite lookup_fmap.
  specialize (Hres l). by apply sqex_cell_nil.
Qed.

Lemma sqex_fresh_block (m : lr_mem) (mu : rw_map) :
  exists l, forall z, m !! (l +ₗ z)%L = None /\ mu !! (l +ₗ z)%L = None.
Proof.
  unfold lr_mem, rw_map in *.
  set (B := (set_map fst (dom m) ∪ set_map fst (dom mu) : gset positive)).
  exists (fresh B, 0%Z). intros z. unfold shift_loc. simpl.
  split; apply not_elem_of_dom_1; intros Hin; apply (is_fresh B);
    [ apply elem_of_union_l | apply elem_of_union_r ];
    change (fresh B) with (fst (fresh B, (0 + z)%Z)); by apply elem_of_map_2.
Qed.

Lemma sqex_step_fresh_reservations (e : expr) (m : lr_mem) (T : list (@mem_ev loc))
    (e' : expr) (m' : lr_mem) (mu : rw_map) :
  lr_step e m T e' m' ->
  exists T' e'' m'', lr_step e m T' e'' m'' /\
    (forall l, lr_alloc_event l ∈ T' -> mu !! l = None).
Proof.
  intros [K a m0 T0 b m1 Hhead]. inversion Hhead; subst.
  - exists [], (fill K (Lit l')), m1. split; first by constructor.
    intros l Hnil. inversion Hnil.
  - exists [], (fill K b), m1. split; first by constructor.
    intros l Hnil. inversion Hnil.
  - exists [lr_read_event l], (fill K (of_val v)), m1. split; first by constructor.
    intros k Hin. apply list_elem_of_singleton in Hin. discriminate.
  - exists [lr_write_event l], (fill K (Lit LitPoison)), (<[l := v]> m0).
    split; first by constructor. intros k Hin. apply list_elem_of_singleton in Hin. discriminate.
  - destruct (sqex_fresh_block m0 mu) as (lfresh & Hfresh).
    exists (lr_alloc_events lfresh (Z.to_nat n)), (fill K (Lit (LitLoc lfresh))),
      (alloc_gmap (LitV LitPoison) lfresh (Z.to_nat n) m0).
    split.
    + apply LREctxStep, LRAllocS; [done | apply Hfresh].
    + intros k Hin. apply list_elem_of_fmap in Hin as (l' & Heq & Hin).
      injection Heq as <-. destruct (sqex_locs_member_range _ _ _ Hin) as (z & Hz & ->).
      apply Hfresh.
  - exists (lr_free_events l (Z.to_nat n)), (fill K (Lit LitPoison)),
      (free_gmap l (Z.to_nat n) m0). split; first by constructor.
    intros k Hin. apply list_elem_of_fmap in Hin as (l' & Heq & _). discriminate.
  - exists [], (fill K b), m1. split; first by constructor.
    intros l Hnil. inversion Hnil.
Qed.

Lemma sqex_step_reservable (e : expr) (m : lr_mem) (T : list (@mem_ev loc))
    (e' : expr) (m' : lr_mem) (mu : rw_map) :
  lr_step e m T e' m' ->
  (forall l, lr_read_event l ∈ T -> exists n, mu !! l = Some (Rst n)) ->
  (forall l, lr_write_event l ∈ T -> mu !! l = Some (Rst 0)) ->
  (forall l, lr_alloc_event l ∈ T -> mu !! l = None) ->
  exists mu', rsv T mu = Some mu'.
Proof.
  intros Hstep Hread Hwrite Halloc.
  destruct (lr_step_mem_effect _ _ _ _ _ Hstep).
  - by exists mu.
  - destruct (Hread l ltac:(by left)) as (n & Hmu).
    exists (<[l := Rst (S n)]> mu).
    change (rsv_Read mu l = Some (<[l := Rst (S n)]> mu)). unfold rsv_Read. by rewrite Hmu.
  - have Hmu := Hwrite l ltac:(by left).
    exists (<[l := Wst]> mu).
    change (rsv_Write mu l = Some (<[l := Wst]> mu)). unfold rsv_Write. by rewrite Hmu.
  - exists (alloc_gmap (Rst 0) l n mu). apply lr_rsv_alloc_events_range.
    intros z Hz. apply Halloc, list_elem_of_fmap_2. by apply lr_locs_member.
  - exists mu. apply lr_rsv_free_events.
Qed.
