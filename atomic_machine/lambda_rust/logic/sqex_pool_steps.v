(** Matching logical threads to physical threads with pending reservations. *)
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_frame.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pending.
From iris.algebra Require Import gmap frac.

Set Default Proof Using "Type".

Definition sqex_trace_budget (T : list (@mem_ev loc)) (p : perm_map) : Prop :=
  (forall l, lr_read_event l ∈ T -> is_Some (p !! l)) /\
  (forall l, lr_write_event l ∈ T -> p !! l = Some 1%Qp).

Definition sqex_thread_matches {Σ} (c : sqex_thread Σ) (t : tstate) : Prop :=
  exists T, t = Running (sqex_thread_expr c) T /\
    sqex_trace_budget T (sqex_thread_perm c).

Definition sqex_pool_matches {Σ} (C : sqex_threads Σ) (tp : tpool) : Prop :=
  map_Forall2 (fun _ => sqex_thread_matches) C tp.

Lemma sqex_trace_budget_nil p : sqex_trace_budget [] p.
Proof. split; intros l Hl; inversion Hl. Qed.

Lemma sqex_trace_budget_alloc l n p : sqex_trace_budget (lr_alloc_events l n) p.
Proof.
  split; intros k Hin; apply list_elem_of_fmap in Hin as (k' & Heq & _); discriminate.
Qed.

Lemma sqex_trace_budget_free l n p : sqex_trace_budget (lr_free_events l n) p.
Proof.
  split; intros k Hin; apply list_elem_of_fmap in Hin as (k' & Heq & _); discriminate.
Qed.

Lemma sqex_step_budgets m T m' p p' :
  lr_mem_effect m T m' -> perm_step T p p' ->
  sqex_trace_budget T p /\ sqex_trace_budget T p' /\
  (forall l, lr_free_event l ∈ T -> p !! l = Some 1%Qp).
Proof.
  intros Heffect Hperm. destruct Heffect.
  - split; first apply sqex_trace_budget_nil. split; first apply sqex_trace_budget_nil.
    intros l Hin. inversion Hin.
  - apply perm_step_singleton in Hperm. inversion Hperm; subst.
    have Hb : sqex_trace_budget [lr_read_event l] p'.
    { split; intros k Hin; apply list_elem_of_singleton in Hin.
      - unfold lr_read_event in Hin. injection Hin as <-. by eexists.
      - discriminate. }
    split; first done. split; first done.
    intros k Hin. apply list_elem_of_singleton in Hin. discriminate.
  - apply perm_step_singleton in Hperm. inversion Hperm; subst.
    have Hb : sqex_trace_budget [lr_write_event l] p'.
    { split; intros k Hin; apply list_elem_of_singleton in Hin.
      - discriminate.
      - unfold lr_write_event in Hin. by injection Hin as <-. }
    split; first done. split; first done.
    intros k Hin. apply list_elem_of_singleton in Hin. discriminate.
  - split; first apply sqex_trace_budget_alloc. split; first apply sqex_trace_budget_alloc.
    intros k Hin. apply list_elem_of_fmap in Hin as (k' & Heq & _). discriminate.
  - split; first apply sqex_trace_budget_free. split; first apply sqex_trace_budget_free.
    intros k Hin. apply list_elem_of_fmap in Hin as (k' & Heq & Hin).
    unfold lr_free_event in Heq. injection Heq as <-.
    by eapply sqex_seq_perm_free_lookup.
Qed.

Lemma sqex_pool_matches_lookup_inv {Σ} (C : sqex_threads Σ) tp i t :
  sqex_pool_matches C tp -> tp !! i = Some t ->
  exists c T, C !! i = Some c /\ t = Running (sqex_thread_expr c) T /\
    sqex_trace_budget T (sqex_thread_perm c).
Proof.
  intros Hmatch Hi. specialize (Hmatch i). rewrite Hi in Hmatch.
  inversion Hmatch as [c t0 Hct|]; subst.
  destruct Hct as (T & -> & Hb). by exists c, T.
Qed.

Lemma sqex_pool_matches_insert {Σ} (C : sqex_threads Σ) tp i c T :
  sqex_pool_matches C tp -> sqex_trace_budget T (sqex_thread_perm c) ->
  sqex_pool_matches (<[i := c]> C) (<[i := Running (sqex_thread_expr c) T]> tp).
Proof.
  intros Hmatch Hb j. destruct (decide (i = j)) as [<-|Hne].
  - rewrite !lookup_insert_eq. constructor. by exists T.
  - rewrite !lookup_insert_ne; [apply Hmatch | done | done].
Qed.

Lemma sqex_pool_matches_commit {Σ} (C : sqex_threads Σ) tp i e T :
  sqex_pool_matches C tp -> tp !! i = Some (Running e T) ->
  sqex_pool_matches C (<[i := Running e []]> tp).
Proof.
  intros Hmatch Hi.
  destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hi) as (c & T' & Hc & He & Hb).
  inversion He; subst. intros j. destruct (decide (i = j)) as [<-|Hne].
  - rewrite lookup_insert_eq Hc. constructor. exists []. split; [done | apply sqex_trace_budget_nil].
  - rewrite lookup_insert_ne; [apply Hmatch | done].
Qed.

Lemma sqex_pool_matches_ready {Σ} (C : sqex_threads Σ) :
  sqex_pool_matches C (sqex_threads_pool C).
Proof.
  intros i. rewrite /sqex_threads_pool lookup_fmap.
  destruct (C !! i) as [c|] eqn:Hi; rewrite Hi /=; constructor.
  exists []. split; [done | apply sqex_trace_budget_nil].
Qed.

Lemma sqex_coherent_full_exclusive {Σ} m p (C : sqex_threads Σ) i j c d l :
  sqex_threads_coherent m p C -> i ≠ j ->
  C !! i = Some c -> C !! j = Some d ->
  sqex_thread_perm c !! l = Some 1%Qp -> sqex_thread_perm d !! l = None.
Proof.
  intros Hcoherent Hne Hc Hd Hfull.
  have Hvalid := sqex_threads_pair_valid _ _ _ _ _ _ _ Hcoherent Hne Hc Hd l.
  destruct (sqex_thread_perm d !! l) as [q|] eqn:Hq; last done.
  have Hrel := proj2 (proj2 (proj2 Hcoherent)) _ _ Hd.
  have Hdom : l ∈ (dom m : gset loc).
  { apply Hrel, elem_of_dom. by exists q. }
  apply elem_of_dom in Hdom as [v Hv].
  rewrite lookup_op !sq_heap_cells_lookup Hfull Hq Hv /= in Hvalid.
  have Hbound : (1 + q ≤ 1)%Qp := proj1 Hvalid.
  exfalso. exact (Qp.not_add_le_l 1 q Hbound).
Qed.

Lemma sqex_ready_no_pending_write {Σ} m p (C : sqex_threads Σ) tp i c e l q :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  C !! i = Some c -> tp !! i = Some (Running e []) ->
  sqex_thread_perm c !! l = Some q ->
  sqex_trace_count SqexWrite l (sqex_pending_events tp) = 0%nat.
Proof.
  intros Hcoherent Hmatch Hc Hi Hq. apply sqex_trace_count_zero. intros Hev.
  apply sqex_pending_events_elem in Hev as (j & e' & T & Hj & Hev).
  have Hne : j ≠ i.
  { intros ->. rewrite Hi in Hj. inversion Hj; subst. inversion Hev. }
  destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hj)
    as (d & U & Hd & He & Hread & Hwrite).
  inversion He; subst. specialize (Hwrite l Hev).
  have Hnone := sqex_coherent_full_exclusive _ _ _ _ _ _ _ _ Hcoherent Hne Hd Hc Hwrite.
  congruence.
Qed.

Lemma sqex_ready_full_no_pending_read {Σ} m p (C : sqex_threads Σ) tp i c e l :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  C !! i = Some c -> tp !! i = Some (Running e []) ->
  sqex_thread_perm c !! l = Some 1%Qp ->
  sqex_trace_count SqexRead l (sqex_pending_events tp) = 0%nat.
Proof.
  intros Hcoherent Hmatch Hc Hi Hfull. apply sqex_trace_count_zero. intros Hev.
  apply sqex_pending_events_elem in Hev as (j & e' & T & Hj & Hev).
  have Hne : i ≠ j.
  { intros <-. rewrite Hi in Hj. inversion Hj; subst. inversion Hev. }
  destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hj)
    as (d & U & Hd & He & Hread & Hwrite).
  inversion He; subst. destruct (Hread l Hev) as [q Hq].
  have Hnone := sqex_coherent_full_exclusive _ _ _ _ _ _ _ _ Hcoherent Hne Hc Hd Hfull.
  congruence.
Qed.

Lemma sqex_ready_readable {Σ} m p (C : sqex_threads Σ) tp mu i c e l q :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu ->
  C !! i = Some c -> tp !! i = Some (Running e []) ->
  sqex_thread_perm c !! l = Some q -> exists n, mu !! l = Some (Rst n).
Proof.
  intros Hcoherent Hmatch Hres Hc Hi Hq.
  have Hzero := sqex_ready_no_pending_write _ _ _ _ _ _ _ _ _ Hcoherent Hmatch Hc Hi Hq.
  have Hrel := proj2 (proj2 (proj2 Hcoherent)) _ _ Hc.
  have [v Hv] : is_Some (m !! l).
  { apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists q. }
  specialize (Hres l). rewrite Hv Hzero in Hres.
  inversion Hres; subst. by eexists.
Qed.

Lemma sqex_ready_writable {Σ} m p (C : sqex_threads Σ) tp mu i c e l :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu ->
  C !! i = Some c -> tp !! i = Some (Running e []) ->
  sqex_thread_perm c !! l = Some 1%Qp -> mu !! l = Some (Rst 0).
Proof.
  intros Hcoherent Hmatch Hres Hc Hi Hfull.
  have HzW := sqex_ready_no_pending_write _ _ _ _ _ _ _ _ _ Hcoherent Hmatch Hc Hi Hfull.
  have HzR := sqex_ready_full_no_pending_read _ _ _ _ _ _ _ _ Hcoherent Hmatch Hc Hi Hfull.
  have Hrel := proj2 (proj2 (proj2 Hcoherent)) _ _ Hc.
  have [v Hv] : is_Some (m !! l).
  { apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists 1%Qp. }
  specialize (Hres l). rewrite Hv HzW HzR in Hres.
  by inversion Hres.
Qed.

Lemma sqex_ready_step_reservable {Σ} m p (C : sqex_threads Σ) tp mu i c e T e' m' local' :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu ->
  C !! i = Some c -> tp !! i = Some (Running e []) ->
  lr_step e m T e' m' -> perm_step T (sqex_thread_perm c) local' ->
  (forall l, lr_alloc_event l ∈ T -> mu !! l = None) ->
  exists mu', rsv T mu = Some mu'.
Proof.
  intros Hcoherent Hmatch Hres Hc Hi Hstep Hperm Halloc.
  destruct (sqex_step_budgets _ _ _ _ _ (lr_step_mem_effect _ _ _ _ _ Hstep) Hperm)
    as [[Hread Hwrite] _].
  eapply sqex_step_reservable; [exact Hstep | | | exact Halloc].
  - intros l Hin. destruct (Hread l Hin) as [q Hq].
    by eapply sqex_ready_readable.
  - intros l Hin. specialize (Hwrite l Hin).
    by eapply sqex_ready_writable.
Qed.

Lemma sqex_ready_step_free_guard {Σ} m p (C : sqex_threads Σ) tp mu i c e T e' m' local' :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu ->
  C !! i = Some c -> tp !! i = Some (Running e []) ->
  lr_step e m T e' m' -> perm_step T (sqex_thread_perm c) local' ->
  forall l, lr_free_event l ∈ T -> mu !! l = Some (Rst 0).
Proof.
  intros Hcoherent Hmatch Hres Hc Hi Hstep Hperm l Hin.
  destruct (sqex_step_budgets _ _ _ _ _ (lr_step_mem_effect _ _ _ _ _ Hstep) Hperm)
    as [_ [_ Hfree]]. specialize (Hfree l Hin).
  by eapply sqex_ready_writable.
Qed.

(** During an external call the executing thread may acquire resources from
    invariants. Its actual precondition must be compatible with the pending
    threads' retained fragments, independently of its previous local map. *)
Definition sqex_access_frame {Σ} m (C : sqex_threads Σ) i l q v : Prop :=
  forall j c, j ≠ i -> C !! j = Some c ->
    ✓ ({[l := (q, to_agree v)]} ⋅ sq_heap_cells m (sqex_thread_perm c)).

Lemma sqex_access_frame_excludes_full {Σ} m (C : sqex_threads Σ) i l q v j c :
  sqex_access_frame m C i l q v -> j ≠ i -> C !! j = Some c ->
  is_Some (m !! l) -> sqex_thread_perm c !! l ≠ Some 1%Qp.
Proof.
  intros Hframe Hne Hc [w Hw] Hfull.
  have Hvalid := Hframe j c Hne Hc l.
  rewrite lookup_op lookup_singleton_eq sq_heap_cells_lookup Hfull Hw /= in Hvalid.
  have Hbound : (q + 1 ≤ 1)%Qp := proj1 Hvalid.
  rewrite Qp.add_comm in Hbound. exact (Qp.not_add_le_l 1 q Hbound).
Qed.

Lemma sqex_access_frame_full_excludes_positive {Σ} m (C : sqex_threads Σ) i l v j c :
  sqex_access_frame m C i l 1%Qp v -> j ≠ i -> C !! j = Some c ->
  is_Some (m !! l) -> sqex_thread_perm c !! l = None.
Proof.
  intros Hframe Hne Hc [w Hw]. apply eq_None_not_Some. intros [q Hq].
  have Hvalid := Hframe j c Hne Hc l.
  rewrite lookup_op lookup_singleton_eq sq_heap_cells_lookup Hq Hw /= in Hvalid.
  have Hbound : (1 + q ≤ 1)%Qp := proj1 Hvalid.
  exact (Qp.not_add_le_l 1 q Hbound).
Qed.

Lemma sqex_access_frame_readable {Σ} m (C : sqex_threads Σ) tp mu i e l q v :
  sqex_access_frame m C i l q v -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu ->
  tp !! i = Some (Running e []) -> is_Some (m !! l) ->
  exists n, mu !! l = Some (Rst n).
Proof.
  intros Hframe Hmatch Hres Hi Hm.
  have HzW : sqex_trace_count SqexWrite l (sqex_pending_events tp) = 0%nat.
  { apply sqex_trace_count_zero. intros Hev.
    apply sqex_pending_events_elem in Hev as (j & e' & T & Hj & Hev).
    have Hne : j ≠ i.
    { intros ->. rewrite Hi in Hj. inversion Hj; subst. inversion Hev. }
    destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hj)
      as (c & U & Hc & He & _ & Hwrite).
    inversion He; subst. specialize (Hwrite l Hev).
    exact (sqex_access_frame_excludes_full _ _ _ _ _ _ _ _ Hframe Hne Hc Hm Hwrite). }
  destruct Hm as [w Hw]. specialize (Hres l). rewrite Hw HzW in Hres.
  inversion Hres; subst. by eexists.
Qed.

Lemma sqex_access_frame_writable {Σ} m (C : sqex_threads Σ) tp mu i e l v :
  sqex_access_frame m C i l 1%Qp v -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu ->
  tp !! i = Some (Running e []) -> is_Some (m !! l) ->
  mu !! l = Some (Rst 0).
Proof.
  intros Hframe Hmatch Hres Hi Hm.
  destruct (sqex_access_frame_readable _ _ _ _ _ _ _ _ _ Hframe Hmatch Hres Hi Hm)
    as [n Hmu].
  have HzR : sqex_trace_count SqexRead l (sqex_pending_events tp) = 0%nat.
  { apply sqex_trace_count_zero. intros Hev.
    apply sqex_pending_events_elem in Hev as (j & e' & T & Hj & Hev).
    have Hne : j ≠ i.
    { intros ->. rewrite Hi in Hj. inversion Hj; subst. inversion Hev. }
    destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hj)
      as (c & U & Hc & He & Hread & _).
    inversion He; subst. destruct (Hread l Hev) as [q Hq].
    have Hnone := sqex_access_frame_full_excludes_positive _ _ _ _ _ _ _ Hframe Hne Hc Hm.
    congruence. }
  specialize (Hres l). rewrite Hmu HzR in Hres.
  by inversion Hres; subst.
Qed.

Definition sqex_posts_extend {Σ} (C C' : sqex_threads Σ) : Prop :=
  forall i c, C !! i = Some c -> exists c', C' !! i = Some c' /\
    sqex_thread_post c = sqex_thread_post c'.

Lemma sqex_posts_extend_trans {Σ} (C1 C2 C3 : sqex_threads Σ) :
  sqex_posts_extend C1 C2 -> sqex_posts_extend C2 C3 -> sqex_posts_extend C1 C3.
Proof.
  intros H12 H23 i c Hc. destruct (H12 _ _ Hc) as (c2 & Hc2 & Hpost).
  destruct (H23 _ _ Hc2) as (c3 & Hc3 & Hpost'). exists c3. split; [done | congruence].
Qed.

Lemma sqex_posts_extend_insert {Σ} (C : sqex_threads Σ) i c e p :
  C !! i = Some c ->
  sqex_posts_extend C (<[i := SqexThread e p (sqex_thread_post c)]> C).
Proof.
  intros Hi j d Hd. destruct (decide (i = j)) as [<-|Hne].
  - rewrite Hi in Hd. injection Hd as <-.
    exists (SqexThread e p (sqex_thread_post c)). split;
      [apply (lookup_insert_eq (M := gmap nat)) | done].
  - exists d. split; [by rewrite lookup_insert_ne | done].
Qed.

Lemma sqex_posts_extend_fresh {Σ} (C : sqex_threads Σ) i c :
  C !! i = None -> sqex_posts_extend C (<[i := c]> C).
Proof.
  intros Hi j d Hd. have Hne : i ≠ j by intros ->; congruence.
  exists d. split; [by rewrite lookup_insert_ne | done].
Qed.

Lemma sqex_result_extend `{!lrSqGS Σ} (C C' : sqex_threads Σ) i t :
  sqex_posts_extend C C' -> sqex_result C' i t -∗ sqex_result C i t.
Proof.
  intros Hextend. iIntros "Hresult" (c e v Hc He Hv).
  destruct (Hextend _ _ Hc) as (c' & Hc' & Hpost).
  rewrite Hpost. iApply ("Hresult" $! c' e v with "[] [] []"); done.
Qed.

(** A Try preserves the whole pure pool invariant. The selected thread's
    permission map follows [perm_step]; every other map is retained. *)
Lemma sqex_pool_seq_successor {Σ} m p (C : sqex_threads Σ) tp mu i c
    T e' m' p' local' mu' :
  sqex_threads_coherent m p C -> sqex_pool_matches C tp ->
  sqex_pool_reservations tp m mu -> C !! i = Some c ->
  tp !! i = Some (Running (sqex_thread_expr c) []) ->
  lr_step (sqex_thread_expr c) m T e' m' ->
  perm_step T p p' -> perm_step T (sqex_thread_perm c) local' ->
  rsv T mu = Some mu' ->
  let C' := <[i := SqexThread e' local' (sqex_thread_post c)]> C in
  let tp' := <[i := Running e' T]> tp in
  sqex_threads_coherent m' p' C' /\ sqex_pool_matches C' tp' /\
    sqex_pool_reservations tp' m' mu' /\ sqex_posts_extend C C'.
Proof.
  intros Hcoherent Hmatch Hres Hc Hi Hstep Hglobal Hlocal Hrsv. simpl.
  split; first by eapply sqex_threads_coherent_seq.
  split.
  - apply sqex_pool_matches_insert; first done.
    exact (proj1 (proj2 (sqex_step_budgets _ _ _ _ _
      (lr_step_mem_effect _ _ _ _ _ Hstep) Hlocal))).
  - split; last by apply sqex_posts_extend_insert.
    eapply sqex_pool_reservations_try; [exact Hres | exact Hi | exact Hstep | | exact Hrsv].
    by eapply sqex_ready_step_free_guard.
Qed.
