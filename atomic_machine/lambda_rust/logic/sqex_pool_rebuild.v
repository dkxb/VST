(** Reconstructing only ready/new threads while preserving the exact maps of
    every framed thread, including threads with pending reservations. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pool_resources.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.

Set Default Proof Using "Type".
Local Existing Instance lr_ext_specs.

Lemma sqex_shapes_lookup {Σ} (C C' : sqex_threads Σ) i c :
  sqex_thread_shapes C' = sqex_thread_shapes C -> C !! i = Some c ->
  exists c', C' !! i = Some c' /\ sqex_thread_expr c' = sqex_thread_expr c /\
    sqex_thread_post c' = sqex_thread_post c.
Proof.
  intros Hsh Hc. have Hi : (sqex_thread_shapes C' !! i : option (sq_expr * (sq_val -> iProp Σ))) =
      sqex_thread_shapes C !! i by rewrite Hsh.
  rewrite /sqex_thread_shapes !lookup_fmap Hc in Hi.
  destruct (C' !! i) as [c'|] eqn:Hc'; rewrite Hc' /= in Hi; last discriminate.
  injection Hi as He Hp. by exists c'.
Qed.

Lemma sqex_shapes_none {Σ} (C C' : sqex_threads Σ) i :
  sqex_thread_shapes C' = sqex_thread_shapes C -> C !! i = None -> C' !! i = None.
Proof.
  intros Hsh Hc. have Hi : (sqex_thread_shapes C' !! i : option (sq_expr * (sq_val -> iProp Σ))) =
      sqex_thread_shapes C !! i by rewrite Hsh.
  rewrite /sqex_thread_shapes !lookup_fmap Hc in Hi.
  destruct (C' !! i) eqn:Hc'; rewrite Hc' /= in Hi; congruence.
Qed.

Section rebuild.
  Context `{!lrSqGS Σ}.

  Lemma sqex_ready_extend m p hF (D : sqex_threads Σ) i e Φ :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> D !! i = None ->
    (forall j c, D !! j = Some c -> sq_heap_rel m (sqex_thread_perm c)) ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    sqex_exact_threads_inv m hF D -∗ EXWP e {{ v, Φ v }} -∗
    ∃ pi : perm_map,
      ⌜sqex_threads_coherent m p (<[i := SqexThread e pi Φ]> D)⌝ ∗
      uPred_ownM (sqex_state_resource m p hF) ∗
      sqex_exact_threads_inv m hF (<[i := SqexThread e pi Φ]> D).
  Proof.
    intros Hnames Hrel Hfresh Hrels. iIntros "Hstate Hothers Hwp".
    set (c0 := SqexThread e ∅ Φ).
    set (C0 := <[i := c0]> D).
    set (F := (dom D : gset nat)).
    have HiF : i ∉ F by apply (proj2 (not_elem_of_dom (M := gmap nat) (D := gset nat) D i)).
    have Hfixedrel : forall j c, C0 !! j = Some c -> j ∈ F ->
        sq_heap_rel m (sqex_thread_perm c).
    { intros j c Hc Hj. have Hne : i ≠ j by intros ->; contradiction.
      rewrite /C0 lookup_insert_ne // in Hc. by eapply Hrels. }
    iDestruct (sqex_threads_reconstruct_mixed _ _ _ C0 F Hnames Hrel Hfixedrel
      with "Hstate [Hothers Hwp]") as (C') "(%Hresult & Hstate & Hthreads)".
    { rewrite /C0 big_sepM_insert // decide_False //.
      iFrame "Hwp". iApply (big_sepM_impl with "Hothers").
      iIntros "!>" (j c Hj) "Hc".
      rewrite decide_True; first done.
      exact (elem_of_dom_2 (M := gmap nat) D j c Hj). }
    destruct Hresult as (Hsh & Hcoherent & Hfixed).
    have Hc0 : C0 !! i = Some c0 by apply (lookup_insert_eq (M := gmap nat)).
    destruct (sqex_shapes_lookup _ _ _ _ Hsh Hc0) as ([e' pi Φ'] & Hi & He & Hp).
    simpl in He, Hp. subst e' Φ'.
    have HC' : C' = <[i := SqexThread e pi Φ]> D.
    { apply (map_eq (M := gmap nat)). intros j.
      destruct (decide (i = j)) as [<-|Hne].
      - by rewrite lookup_insert_eq.
      - rewrite lookup_insert_ne //.
        destruct (D !! j) as [c|] eqn:Hj.
        + rewrite Hfixed; [by rewrite /C0 lookup_insert_ne // |].
          exact (elem_of_dom_2 (M := gmap nat) D j c Hj).
        + rewrite Hj. apply (sqex_shapes_none C0 C' j Hsh). by rewrite /C0 lookup_insert_ne. }
    subst C'. iExists pi. by iFrame.
  Qed.

  Lemma sqex_ready_replace m p hF (C : sqex_threads Σ) tp i c e' :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> C !! i = Some c ->
    (forall j d, delete i C !! j = Some d -> sq_heap_rel m (sqex_thread_perm d)) ->
    sqex_pool_matches C tp ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    sqex_exact_threads_inv m hF (delete i C) -∗
    EXWP e' {{ v, sqex_thread_post c v }} -∗
    ∃ pi : perm_map,
      ⌜sqex_threads_coherent m p (<[i := SqexThread e' pi (sqex_thread_post c)]> C) ∧
        sqex_pool_matches (<[i := SqexThread e' pi (sqex_thread_post c)]> C)
          (<[i := Running e' []]> tp) ∧
        sqex_posts_extend C (<[i := SqexThread e' pi (sqex_thread_post c)]> C)⌝ ∗
      uPred_ownM (sqex_state_resource m p hF) ∗
      sqex_exact_threads_inv m hF (<[i := SqexThread e' pi (sqex_thread_post c)]> C).
  Proof.
    intros Hnames Hrel Hi Hrels Hmatch. iIntros "Hstate Hothers Hwp".
    iDestruct (sqex_ready_extend _ _ _ (delete i C) i e' (sqex_thread_post c)
      Hnames Hrel (lookup_delete_eq C i) Hrels with "Hstate Hothers Hwp")
      as (pi) "(%Hcoherent & Hstate & Hthreads)".
    rewrite insert_delete_eq in Hcoherent.
    iEval (rewrite insert_delete_eq) in "Hthreads".
    iExists pi. iFrame. iPureIntro. split; first done. split.
    - apply sqex_pool_matches_insert; [done | apply sqex_trace_budget_nil].
    - by apply sqex_posts_extend_insert.
  Qed.

  Lemma sqex_ready_spawn m p hF (C : sqex_threads Σ) tp i c j parent child :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> C !! i = Some c ->
    C !! j = None ->
    (forall k d, delete i C !! k = Some d -> sq_heap_rel m (sqex_thread_perm d)) ->
    sqex_pool_matches C tp ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    sqex_exact_threads_inv m hF (delete i C) -∗
    EXWP parent {{ v, sqex_thread_post c v }} -∗ EXWP child {{ _, True }} -∗
    ∃ pp pc : perm_map,
      let C' := <[j := SqexThread child pc (fun _ => True%I)]>
        (<[i := SqexThread parent pp (sqex_thread_post c)]> C) in
      ⌜sqex_threads_coherent m p C' ∧
        sqex_pool_matches C' (<[j := Running child []]> (<[i := Running parent []]> tp)) ∧
        sqex_posts_extend C C'⌝ ∗
      uPred_ownM (sqex_state_resource m p hF) ∗ sqex_exact_threads_inv m hF C'.
  Proof.
    intros Hnames Hrel Hi Hj Hrels Hmatch. iIntros "Hstate Hothers Hparent Hchild".
    have Hne : i ≠ j by intros ->; congruence.
    iDestruct (sqex_ready_replace _ _ _ _ _ _ _ _ Hnames Hrel Hi Hrels Hmatch
      with "Hstate Hothers Hparent") as (pp) "(%Hparent & Hstate & Hthreads)".
    destruct Hparent as (Hcoherent & Hmatch' & Hposts).
    set (D := <[i := SqexThread parent pp (sqex_thread_post c)]> C).
    have HjD : D !! j = None by rewrite /D lookup_insert_ne.
    have HrelsD : forall k d, D !! k = Some d -> sq_heap_rel m (sqex_thread_perm d).
    { exact (proj2 (proj2 (proj2 Hcoherent))). }
    iDestruct (sqex_ready_extend _ _ _ D j child (fun _ => True%I)
      Hnames Hrel HjD HrelsD with "Hstate Hthreads Hchild")
      as (pc) "(%Hcoherent' & Hstate & Hthreads)".
    iExists pp, pc. simpl. iFrame. iPureIntro. split; first done. split.
    - apply sqex_pool_matches_insert; [exact Hmatch' | apply sqex_trace_budget_nil].
    - eapply sqex_posts_extend_trans; first exact Hposts.
      by apply sqex_posts_extend_fresh.
  Qed.
End rebuild.
