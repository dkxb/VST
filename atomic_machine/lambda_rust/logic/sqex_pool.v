(** Collections of compatible logical threads, indexed by machine thread ID. *)
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_rules.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_resources.
From iris.algebra Require Import big_op.
From iris.algebra Require Import gmap frac agree.
From iris.algebra Require Import local_updates.

Set Default Proof Using "Type".
Local Existing Instance lr_ext_specs.

Record sqex_thread (Σ : gFunctors) := SqexThread {
  sqex_thread_expr : sq_expr;
  sqex_thread_perm : perm_map;
  sqex_thread_post : sq_val -> iProp Σ
}.
Arguments SqexThread {_} _ _ _.
Arguments sqex_thread_expr {_} _.
Arguments sqex_thread_perm {_} _.
Arguments sqex_thread_post {_} _ _.

Definition sqex_threads Σ := gmap nat (sqex_thread Σ).

Definition sqex_threads_pool {Σ} (C : sqex_threads Σ) : tpool :=
  (fun c => Running (sqex_thread_expr c) []) <$> C.

Definition sqex_threads_cells {Σ} (m : lr_mem) (C : sqex_threads Σ) : sq_heapUR :=
  [^op map] c ∈ C, sq_heap_cells m (sqex_thread_perm c).

(** The unused part of the authority may belong to shared invariants or be
    unclaimed. The sum of the thread permissions is included in the authority. *)
Definition sqex_threads_coherent {Σ} (m : lr_mem) (p : perm_map)
    (C : sqex_threads Σ) : Prop :=
  sq_heap_rel m p ∧ ✓ sq_heap_cells m p ∧
  sqex_threads_cells m C ≼ sq_heap_cells m p ∧
  forall i c, C !! i = Some c -> sq_heap_rel m (sqex_thread_perm c).

Lemma sqex_threads_coherent_singleton {Σ} m p i e (Φ : sq_val -> iProp Σ) :
  sq_heap_rel m p -> ✓ sq_heap_cells m p ->
  sqex_threads_coherent m p {[i := SqexThread e p Φ]}.
Proof.
  intros Hrel Hvalid. split; first done. split; first done. split.
  - rewrite /sqex_threads_cells big_opM_singleton /=. done.
  - intros j c Hc. apply (lookup_singleton_Some (M := gmap nat)) in Hc as [-> <-]. done.
Qed.

Lemma sqex_heap_cells_update_unowned m p l v :
  p !! l = None -> sq_heap_cells (<[l := v]> m) p = sq_heap_cells m p.
Proof.
  intros Hl. apply (map_eq (M := gmap loc)). intros k.
  rewrite !sq_heap_cells_lookup.
  destruct (decide (l = k)) as [<-|Hne].
  - by rewrite Hl.
  - by rewrite lookup_insert_ne.
Qed.

(** Recovering a permission map from a compatible heap fragment is the
    algebraic part of redistributing the resources after an external call. *)
Definition sqex_fragment_permissions (h : sq_heapUR) : perm_map := fst <$> h.

Lemma sqex_fragment_lookup m p (h : sq_heapUR) l q a :
  h ≼ sq_heap_cells m p -> h !! l = Some (q, a) ->
  exists v, m !! l = Some v ∧ a ≡ to_agree v.
Proof.
  intros Hinc Hl. have Hin := proj1 (lookup_included _ _) Hinc l.
  rewrite Hl in Hin. destruct (Some_included_is_Some _ _ Hin) as [x Hx].
  rewrite sq_heap_cells_lookup in Hx.
  destruct (p !! l) eqn:Hp; simpl in Hx; last discriminate.
  destruct (m !! l) as [v|] eqn:Hm; simpl in Hx; last discriminate.
  rewrite sq_heap_cells_lookup Hp Hm /= in Hin.
  exists v. split; first done. apply Some_included in Hin as [Heq|Hpart].
  - exact (proj2 Heq).
  - apply pair_included in Hpart as [_ Ha].
    eapply agree_valid_included; [done | exact Ha].
Qed.

Lemma sqex_fragment_representation m p h :
  h ≼ sq_heap_cells m p ->
  sq_heap_rel m (sqex_fragment_permissions h) ∧
  sq_heap_cells m (sqex_fragment_permissions h) ≡ h.
Proof.
  intros Hinc. split.
  - intros l Hl. apply elem_of_dom in Hl as [q Hq].
    rewrite /sqex_fragment_permissions lookup_fmap in Hq.
    apply fmap_Some in Hq as ([q0 a] & Hh & _).
    destruct (sqex_fragment_lookup _ _ _ _ _ _ Hinc Hh) as (v & Hv & _).
    apply elem_of_dom. by exists v.
  - intros l. rewrite sq_heap_cells_lookup /sqex_fragment_permissions lookup_fmap.
    destruct (h !! l) as [[q a]|] eqn:Hl; rewrite Hl /=; last done.
    destruct (sqex_fragment_lookup _ _ _ _ _ _ Hinc Hl) as (v & Hv & Ha).
    rewrite Hv /=. apply Some_proper. split; first done. by symmetry.
Qed.

Lemma sqex_threads_pair_valid {Σ} m p (C : sqex_threads Σ) i j c1 c2 :
  sqex_threads_coherent m p C -> i ≠ j ->
  C !! i = Some c1 -> C !! j = Some c2 ->
  ✓ (sq_heap_cells m (sqex_thread_perm c1) ⋅ sq_heap_cells m (sqex_thread_perm c2)).
Proof.
  intros (_ & Hvalid & Hsum & _) Hne Hi Hj.
  have Hvalid_sum : ✓ sqex_threads_cells m C by eapply cmra_valid_included.
  have Hj' : delete i C !! j = Some c2 by rewrite lookup_delete_ne.
  rewrite /sqex_threads_cells (big_opM_delete _ C i c1 Hi)
    (big_opM_delete _ (delete i C) j c2 Hj') assoc in Hvalid_sum.
  by apply cmra_valid_op_l in Hvalid_sum.
Qed.

(** A local update of the selected heap fragment preserves compatibility
    with the sum of the unchanged threads and the unclaimed heap frame. *)
Lemma sqex_threads_coherent_local_update {Σ} m m' p p' (C : sqex_threads Σ) i c c' :
  C !! i = Some c -> sqex_threads_coherent m p C ->
  (sq_heap_cells m p, sq_heap_cells m (sqex_thread_perm c)) ~l~>
    (sq_heap_cells m' p', sq_heap_cells m' (sqex_thread_perm c')) ->
  (forall j d, delete i C !! j = Some d ->
    sq_heap_cells m' (sqex_thread_perm d) ≡ sq_heap_cells m (sqex_thread_perm d) ∧
    sq_heap_rel m' (sqex_thread_perm d)) ->
  sq_heap_rel m' p' -> sq_heap_rel m' (sqex_thread_perm c') ->
  sqex_threads_coherent m' p' (<[i := c']> C).
Proof.
  intros Hi (_ & Hvalid & Hsum & _) Hupdate Hframe Hrel Hrelc.
  rewrite /sqex_threads_cells (big_opM_delete _ C i c Hi) in Hsum.
  destruct Hsum as [f Hsum].
  rewrite local_update_unital_discrete in Hupdate.
  destruct (Hupdate (sqex_threads_cells m (delete i C) ⋅ f) Hvalid)
    as [Hvalid' Hsum']; first by rewrite /sqex_threads_cells assoc.
  have Hframes : sqex_threads_cells m' (delete i C) ≡ sqex_threads_cells m (delete i C).
  { unfold sqex_threads_cells. apply (big_opM_proper (M := sq_heapUR)). intros j d Hj. exact (proj1 (Hframe _ _ Hj)). }
  split; first done. split; first done. split.
  - exists f. rewrite /sqex_threads_cells big_opM_insert_delete.
    rewrite /sqex_threads_cells in Hframes. rewrite Hframes -assoc. exact Hsum'.
  - intros j d Hj. apply (lookup_insert_Some (M := gmap nat)) in Hj as [[-> <-]|[Hne Hj]].
    + exact Hrelc.
    + have Hd : delete i C !! j = Some d by rewrite lookup_delete_ne.
      exact (proj2 (Hframe _ _ Hd)).
Qed.

Section thread_resources.
  Context `{!lrSqGS Σ}.

  Definition sqex_result (C : sqex_threads Σ) (i : nat) (t : tstate) : iProp Σ :=
    ∀ c e v, ⌜C !! i = Some c⌝ -∗ ⌜t = Running e []⌝ -∗
      ⌜to_val e = Some v⌝ -∗ sqex_thread_post c v.

  Definition sqex_thread_inv m hF (c : sqex_thread Σ) : iProp Σ :=
    ∃ r : iResUR Σ, uPred_ownM r ∗
      sqex_support (EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}) r ∗
      sqex_resource_fits m (sqex_thread_perm c) hF r.

  Lemma sqex_thread_inv_wp m hF c :
    sqex_thread_inv m hF c -∗
    EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}.
  Proof. iIntros "(%r & Hr & Hsupport & _)". by iApply (sqex_support_elim with "Hr Hsupport"). Qed.

  (** Testing the selected thread's resource witness proves permission
      requirements against its own map, even while other WPs are framed. *)
  Lemma sqex_thread_inv_permissions m hF c T e' m' :
    sq_heap_rel m (sqex_thread_perm c) -> sq_freeable_rel m hF ->
    lr_step (sqex_thread_expr c) m T e' m' ->
    sqex_thread_inv m hF c -∗
      ▷ ⌜exists p', perm_step T (sqex_thread_perm c) p'⌝.
  Proof.
    intros Hrel HFrel Hstep. iIntros "(%r & _ & Hsupport & Hfit)".
    iApply plainly_elim.
    iApply (sqex_support_test (sqex_state_resource m (sqex_thread_perm c) hF) r
      (EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }})
      (▷ ⌜exists p', perm_step T (sqex_thread_perm c) p'⌝)%I
      with "[Hsupport Hfit]").
    - iIntros "[Hstate Hwp]". iApply plain.
      iApply (exwp_step_permissions ⊤ _ _ _ _ _ _ _
        (lr_step_not_value _ _ _ _ _ Hstep)
        (lr_step_not_external _ _ _ _ _ Hstep) Hstep with "[Hstate] Hwp").
      by iApply (sqex_state_resource_heap _ _ _ Hrel HFrel with "Hstate").
    - by iSplit.
  Qed.
End thread_resources.
