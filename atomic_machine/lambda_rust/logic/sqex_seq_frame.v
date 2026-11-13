(** Sequential permission updates preserve the other threads' permission maps.
    This file contains only the pure camera and memory part of that argument. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pool.
Require Import VST.atomic_machine.lambda_rust.equivalence.
From iris.algebra Require Import local_updates gmap frac agree.

Set Default Proof Using "Type".

Lemma sqex_seq_range_offset l n k :
  loc_in_range l n k ->
  exists z, (0 <= z < Z.of_nat n)%Z /\ k = (l +ₗ z)%L.
Proof.
  destruct l as [b o], k as [b' o']; unfold loc_in_range, shift_loc; simpl.
  intros [-> Hrange]. exists (o' - o)%Z. split; [lia | f_equal; lia].
Qed.

Lemma sqex_seq_alloc_insert p l n k :
  alloc_gmap 1%Qp l n (<[k := 1%Qp]> p) =
    <[k := 1%Qp]> (alloc_gmap 1%Qp l n p).
Proof.
  revert l. induction n as [|n IH]=> l //=. rewrite IH.
  destruct (decide (l = k)) as [->|Hne]; first done.
  by rewrite insert_insert_ne.
Qed.

Lemma sqex_seq_free_delete (p : perm_map) l n k :
  free_gmap l n (delete k p) = delete k (free_gmap l n p).
Proof. revert l. induction n as [|n IH]=> l //=. by rewrite IH delete_delete. Qed.

Lemma sqex_seq_perm_alloc_result l n p p' :
  perm_step (lr_alloc_events l n) p p' -> p' = alloc_gmap 1%Qp l n p.
Proof.
  revert l p p'. induction n as [|n IH]=> l p p' Hperm.
  - by inversion Hperm.
  - inversion Hperm as [|ev T p1 p2 p3 Hev Htail]; subst.
    inversion Hev; subst. rewrite (IH _ _ _ Htail) /=. apply sqex_seq_alloc_insert.
Qed.

Lemma sqex_seq_perm_free_result l n p p' :
  perm_step (lr_free_events l n) p p' -> p' = free_gmap l n p.
Proof.
  revert l p p'. induction n as [|n IH]=> l p p' Hperm.
  - by inversion Hperm.
  - inversion Hperm as [|ev T p1 p2 p3 Hev Htail]; subst.
    inversion Hev; subst. rewrite (IH _ _ _ Htail) /=. apply sqex_seq_free_delete.
Qed.

Lemma sqex_seq_perm_free_lookup ls p p' l :
  perm_step (lr_free_event <$> ls) p p' -> l ∈ ls -> p !! l = Some 1%Qp.
Proof.
  revert p p'. induction ls as [|k ls IH]=> p p' Hperm Hl; first inversion Hl.
  inversion Hperm as [|ev T p1 p2 p3 Hev Htail]; subst.
  inversion Hev; subst.
  apply elem_of_cons in Hl as [->|Hl]; first done.
  apply IH in Htail; last done.
  by apply lookup_delete_Some in Htail as [_ Htail].
Qed.

Lemma sqex_seq_full_frame m p frame l :
  sq_heap_rel m frame -> p !! l = Some 1%Qp ->
  ✓ (sq_heap_cells m p ⋅ sq_heap_cells m frame) -> frame !! l = None.
Proof.
  intros Hrel Hp Hvalid. apply eq_None_not_Some. intros [q Hq].
  have [v Hv] : is_Some (m !! l).
  { apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists q. }
  specialize (Hvalid l).
  rewrite lookup_op !sq_heap_cells_lookup Hp Hq Hv /= in Hvalid.
  have Hbound : (1 + q ≤ 1)%Qp := proj1 Hvalid.
  exact (Qp.not_add_le_l 1 q Hbound).
Qed.

Lemma sqex_seq_heap_rel m T m' p p' :
  lr_mem_effect m T m' -> perm_step T p p' ->
  sq_heap_rel m p -> sq_heap_rel m' p'.
Proof.
  intros Heffect Hperm Hrel. destruct Heffect.
  - by inversion Hperm; subst.
  - apply perm_step_singleton in Hperm. by inversion Hperm; subst.
  - apply perm_step_singleton in Hperm. inversion Hperm; subst.
    unfold sq_heap_rel, lr_mem, perm_map in *. rewrite dom_insert_L. set_solver.
  - rewrite (sqex_seq_perm_alloc_result _ _ _ _ Hperm).
    intros k Hk. apply elem_of_dom in Hk as [q Hq].
    rewrite sq_mem_lookup_init_mem in Hq. apply elem_of_dom.
    rewrite sq_mem_lookup_init_mem. case_decide; first by eexists.
    apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists q.
  - rewrite (sqex_seq_perm_free_result _ _ _ _ Hperm).
    intros k Hk. apply elem_of_dom in Hk as [q Hq].
    rewrite sq_mem_lookup_free_mem in Hq. apply elem_of_dom.
    rewrite sq_mem_lookup_free_mem. case_decide; first discriminate.
    apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists q.
Qed.

Lemma sqex_seq_cells_local_update m T m' p p' local local' :
  lr_mem_effect m T m' -> perm_step T p p' -> perm_step T local local' ->
  (sq_heap_cells m p, sq_heap_cells m local) ~l~>
    (sq_heap_cells m' p', sq_heap_cells m' local').
Proof.
  intros Heffect Hglobal Hlocal. destruct Heffect.
  - inversion Hglobal; inversion Hlocal; subst. done.
  - apply perm_step_singleton in Hglobal, Hlocal.
    inversion Hglobal; inversion Hlocal; subst. done.
  - apply perm_step_singleton in Hglobal, Hlocal.
    inversion Hglobal as [|pg lg HG| |]; subst.
    inversion Hlocal as [|pl ll HL| |]; subst.
    destruct H as [old Hold].
    rewrite (sq_heap_cells_write _ _ _ _ _ HG) (sq_heap_cells_write _ _ _ _ _ HL).
    eapply insert_local_update with (x := (1%Qp, to_agree old))
      (y := (1%Qp, to_agree old)).
    + by rewrite sq_heap_cells_lookup HG Hold.
    + by rewrite sq_heap_cells_lookup HL Hold.
    + apply exclusive_local_update. done.
  - rewrite (sqex_seq_perm_alloc_result _ _ _ _ Hglobal)
      (sqex_seq_perm_alloc_result _ _ _ _ Hlocal).
    apply gmap_local_update. intros k.
    rewrite !sq_heap_cells_lookup !sq_mem_lookup_init_mem.
    case_decide as Hrange; last done. simpl.
    destruct (sqex_seq_range_offset _ _ _ Hrange) as (z & _ & ->).
    rewrite H. destruct (p !! (l +ₗ z)) eqn:Hp; rewrite ?Hp /=;
      apply alloc_option_local_update; done.
  - have Hp' := sqex_seq_perm_free_result _ _ _ _ Hglobal.
    have Hl' := sqex_seq_perm_free_result _ _ _ _ Hlocal.
    rewrite Hp' Hl'. apply gmap_local_update. intros k.
    rewrite !sq_heap_cells_lookup !sq_mem_lookup_free_mem.
    case_decide as Hrange; last done. simpl.
    destruct (sqex_seq_range_offset _ _ _ Hrange) as (z & Hz & ->).
    have Hloc : local !! (l +ₗ z) = Some 1%Qp.
    { eapply sqex_seq_perm_free_lookup; [exact Hlocal | by apply lr_locs_member]. }
    destruct (H z Hz) as [old Hold]. rewrite Hloc Hold /=.
    apply delete_option_local_update. apply _.
Qed.

Lemma sqex_seq_frame_lookup m T m' p p' frame k q :
  lr_mem_effect m T m' -> perm_step T p p' ->
  sq_heap_rel m frame -> ✓ (sq_heap_cells m p ⋅ sq_heap_cells m frame) ->
  frame !! k = Some q -> m' !! k = m !! k.
Proof.
  intros Heffect Hperm Hrel Hvalid Hframe. destruct Heffect; try done.
  - apply perm_step_singleton in Hperm. inversion Hperm as [|pl ll Hfull| |]; subst.
    have Hnone := sqex_seq_full_frame _ _ _ _ Hrel Hfull Hvalid.
    apply lookup_insert_ne. congruence.
  - rewrite sq_mem_lookup_init_mem. case_decide as Hrange; last done.
    destruct (sqex_seq_range_offset _ _ _ Hrange) as (z & _ & ->).
    have [v Hv] : is_Some (m !! (l +ₗ z)).
    { apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists q. }
    rewrite H in Hv. discriminate.
  - rewrite sq_mem_lookup_free_mem. case_decide as Hrange; last done.
    destruct (sqex_seq_range_offset _ _ _ Hrange) as (z & Hz & ->).
    have Hp : p !! (l +ₗ z) = Some 1%Qp.
    { eapply sqex_seq_perm_free_lookup; [exact Hperm | by apply lr_locs_member]. }
    have Hnone := sqex_seq_full_frame _ _ _ _ Hrel Hp Hvalid. congruence.
Qed.

Lemma sqex_seq_frame m T m' p p' frame :
  lr_mem_effect m T m' -> perm_step T p p' ->
  sq_heap_rel m frame -> ✓ (sq_heap_cells m p ⋅ sq_heap_cells m frame) ->
  sq_heap_cells m' frame = sq_heap_cells m frame /\ sq_heap_rel m' frame.
Proof.
  intros Heffect Hperm Hrel Hvalid. split.
  - apply (map_eq (M := gmap loc)). intros k. rewrite !sq_heap_cells_lookup.
    destruct (frame !! k) as [q|] eqn:Hq; simpl; last done.
    by rewrite (sqex_seq_frame_lookup _ _ _ _ _ _ _ _ Heffect Hperm Hrel Hvalid Hq).
  - intros k Hk. apply elem_of_dom in Hk as [q Hq].
    apply elem_of_dom.
    rewrite (sqex_seq_frame_lookup _ _ _ _ _ _ _ _ Heffect Hperm Hrel Hvalid Hq).
    apply (elem_of_dom (D := gset loc)), Hrel, elem_of_dom. by exists q.
Qed.

Lemma sqex_threads_coherent_seq {Σ} m m' p p' (C : sqex_threads Σ) i c e' T local' :
  C !! i = Some c -> sqex_threads_coherent m p C ->
  lr_step (sqex_thread_expr c) m T e' m' ->
  perm_step T p p' -> perm_step T (sqex_thread_perm c) local' ->
  sqex_threads_coherent m' p'
    (<[i := SqexThread e' local' (sqex_thread_post c)]> C).
Proof.
  intros Hi Hcoherent Hstep Hglobal Hlocal.
  have Heffect := lr_step_mem_effect _ _ _ _ _ Hstep.
  eapply sqex_threads_coherent_local_update; [exact Hi | exact Hcoherent | | | | ].
  - by eapply sqex_seq_cells_local_update.
  - intros j d Hj. apply (lookup_delete_Some (M := gmap nat)) in Hj as [Hne Hj].
    destruct (sqex_seq_frame _ _ _ _ _ (sqex_thread_perm d)
      Heffect Hlocal (proj2 (proj2 (proj2 Hcoherent)) _ _ Hj)) as [Heq Hrel].
    + by eapply sqex_threads_pair_valid.
    + by split; first rewrite Heq.
  - eapply sqex_seq_heap_rel; [exact Heffect | exact Hglobal | exact (proj1 Hcoherent)].
  - eapply sqex_seq_heap_rel; [exact Heffect | exact Hlocal | ].
    by eapply (proj2 (proj2 (proj2 Hcoherent))).
Qed.
