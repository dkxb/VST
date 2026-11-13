(** External-call steps against the concrete contracts, with pending threads. *)
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pool_resources.
From iris.algebra Require Import auth gmap frac agree local_updates.

Set Default Proof Using "Type".
Local Existing Instance lr_ext_specs.

Section external_steps.
  Context `{!lrSqGS Σ}.

  Lemma sqex_state_lookup m p hF l q v :
    sq_heap_rel m p -> sq_freeable_rel m hF ->
    uPred_ownM (sqex_state_resource m p hF) -∗ l ↦{q} v -∗
    ⌜m !! l = Some v ∧ exists qt, p !! l = Some qt ∧ (q ≤ qt ≤ 1)%Qp⌝.
  Proof.
    intros Hrel HFrel. iIntros "Hstate Hl".
    iApply (sq_heap_gen_lookup with "[Hstate] Hl").
    by iApply (sqex_state_resource_heap with "Hstate").
  Qed.

  Lemma sqex_state_write m p hF l old v :
    sq_heap_rel m p -> sq_freeable_rel m hF ->
    uPred_ownM (sqex_state_resource m p hF) -∗ l ↦ old ==∗
    uPred_ownM (sqex_state_resource (<[l := v]> m) p hF) ∗ l ↦ v.
  Proof.
    intros Hrel HFrel. iIntros "Hstate Hl".
    iDestruct (sqex_state_lookup with "Hstate Hl") as %(Hm & qt & Hp & Hlo & Hhi);
      [done | done |].
    have Hq : qt = 1%Qp by apply (anti_symm (≤)%Qp). subst qt.
    iEval (rewrite sqex_state_resource_own) in "Hstate".
    iDestruct "Hstate" as "[Hm HF]".
    iMod (own_update_2 with "Hm Hl") as "[Hm Hl]".
    { apply auth_update, (singleton_local_update _ _ (1%Qp, to_agree old)).
      - by rewrite sq_heap_cells_lookup Hp Hm.
      - apply (exclusive_local_update _ (1%Qp, to_agree v)). done. }
    iModIntro. rewrite sqex_state_resource_own (sq_heap_cells_write _ _ _ _ _ Hp).
    by iFrame.
  Qed.

  Lemma sqex_exact_thread_inv_update_unowned m hF c l v :
    sqex_thread_perm c !! l = None ->
    sqex_exact_thread_inv (<[l := v]> m) hF c ⊣⊢ sqex_exact_thread_inv m hF c.
  Proof.
    intros Hl. rewrite /sqex_exact_thread_inv /sqex_resource_fits
      /sqex_state_resource /sqex_heap_resource.
    by rewrite (sqex_heap_cells_update_unowned _ _ _ _ Hl).
  Qed.

  Lemma sqex_exact_threads_inv_write_frame m hF C i l old v :
    sqex_access_frame m C i l 1%Qp old -> is_Some (m !! l) ->
    sqex_exact_threads_inv (<[l := v]> m) hF (delete i C) ⊣⊢
      sqex_exact_threads_inv m hF (delete i C).
  Proof.
    intros Hframe Hm. apply big_sepM_proper.
    intros j c Hj. apply (lookup_delete_Some (M := gmap nat)) in Hj as [Hne Hj].
    apply sqex_exact_thread_inv_update_unowned.
    eapply sqex_access_frame_full_excludes_positive; eauto.
  Qed.

  Lemma sqex_external_read_pending E C tp m p hF mu i e k l Φ :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> sq_freeable_rel m hF ->
    ✓ sq_heap_cells m p -> sqex_pool_matches C tp -> sqex_pool_reservations tp m mu ->
    tp !! i = Some (Running e []) -> lr_external e (ALoad tt l) k ->
    uPred_ownM (sqex_state_resource m p hF) -∗ EXWP e @ E {{ Φ }} -∗
    sqex_exact_threads_inv m hF (delete i C) ={E,∅}=∗ ∃ v,
      ⌜m !! l = Some v /\ at_step (AMCfg tp m mu)
        (AMCfg (<[i := Running (k (Some v)) []]> tp) m mu)⌝ ∗
      ▷ |={∅,E}=> uPred_ownM (sqex_state_resource m p hF) ∗
        EXWP k (Some v) @ E {{ Φ }} ∗ sqex_exact_threads_inv m hF (delete i C).
  Proof.
    intros Hnames Hrel HFrel Hvalid Hmatch Hres Hi He.
    iIntros "Hstate Hwp Hothers". rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod "Hwp" as ([q v]) "[Hl Hcont]". simpl.
    iDestruct (sqex_state_lookup with "Hstate Hl") as %[Hm _]; [done | done |].
    iDestruct (sqex_exact_access_frame with "Hstate Hl Hothers") as %Hframe;
      [exact Hnames | exact Hvalid |].
    have [n Hmu] := sqex_access_frame_readable _ _ _ _ _ _ _ _ _
      Hframe Hmatch Hres Hi (ex_intro _ v Hm).
    iModIntro. iExists v. iSplit.
    { iPureIntro. split; first done. eapply SC_Read; [exact Hi | exact He | | exact Hm].
      apply Forall_singleton. by rewrite Hmu. }
    iNext. iMod ("Hcont" $! (Some v) with "[Hl]") as "Hwp".
    { simpl. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma sqex_external_write_pending E C tp m p hF mu i e k l v Φ :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> sq_freeable_rel m hF ->
    ✓ sq_heap_cells m p -> sqex_pool_matches C tp -> sqex_pool_reservations tp m mu ->
    tp !! i = Some (Running e []) -> lr_external e (AStore tt l v) k ->
    uPred_ownM (sqex_state_resource m p hF) -∗ EXWP e @ E {{ Φ }} -∗
    sqex_exact_threads_inv m hF (delete i C) ={E,∅}=∗
      ⌜is_Some (m !! l) /\ at_step (AMCfg tp m mu)
        (AMCfg (<[i := Running (k None) []]> tp) (<[l := v]> m) mu)⌝ ∗
      ▷ |={∅,E}=> uPred_ownM (sqex_state_resource (<[l := v]> m) p hF) ∗
        EXWP k None @ E {{ Φ }} ∗
        sqex_exact_threads_inv (<[l := v]> m) hF (delete i C).
  Proof.
    intros Hnames Hrel HFrel Hvalid Hmatch Hres Hi He.
    iIntros "Hstate Hwp Hothers". rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod "Hwp" as (old) "[Hl Hcont]". simpl.
    iDestruct (sqex_state_lookup with "Hstate Hl") as %[Hm _]; [done | done |].
    iDestruct (sqex_exact_access_frame with "Hstate Hl Hothers") as %Hframe;
      [exact Hnames | exact Hvalid |].
    have Hmu := sqex_access_frame_writable _ _ _ _ _ _ _ _
      Hframe Hmatch Hres Hi (ex_intro _ old Hm).
    iMod (sqex_state_write with "Hstate Hl") as "[Hstate Hl]"; [done | done |].
    iEval (rewrite -(sqex_exact_threads_inv_write_frame _ _ _ _ _ _ v Hframe
      (ex_intro _ old Hm))) in "Hothers".
    iModIntro. iSplit.
    { iPureIntro. split; first by exists old.
      eapply SC_Write; [exact Hi | exact He | |].
      - apply Forall_singleton. exact Hmu.
      - by rewrite /= Hm. }
    iNext. iMod ("Hcont" $! None with "[Hl]") as "Hwp".
    { simpl. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma sqex_external_cas_suc_pending E C tp m p hF mu i e k l ve vn old Φ :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> sq_freeable_rel m hF ->
    ✓ sq_heap_cells m p -> sqex_pool_matches C tp -> sqex_pool_reservations tp m mu ->
    tp !! i = Some (Running e []) -> lr_external e (ACAS tt l ve vn) k ->
    m !! l = Some old -> lr_val_eq m old ve ->
    uPred_ownM (sqex_state_resource m p hF) -∗ EXWP e @ E {{ Φ }} -∗
    sqex_exact_threads_inv m hF (delete i C) ={E,∅}=∗
      ▷ |={∅,E}=> uPred_ownM (sqex_state_resource (<[l := vn]> m) p hF) ∗
        EXWP k (Some (LitV (LitInt 1))) @ E {{ Φ }} ∗
        sqex_exact_threads_inv (<[l := vn]> m) hF (delete i C).
  Proof.
    intros Hnames Hrel HFrel Hvalid Hmatch Hres Hi He Hload Heq.
    iIntros "Hstate Hwp Hothers". rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod "Hwp" as ([cur expected]) "[[%Hexpected Hl] Hcont]". simpl in Hexpected.
    iDestruct (sqex_state_lookup with "Hstate Hl") as %[Hm _]; [done | done |].
    simpl in Hm. have Hold : old = LitV (LitInt cur) by congruence.
    have Hsame : cur = expected.
    { rewrite Hold Hexpected /lr_val_eq in Heq. by inversion Heq. }
    subst expected.
    iDestruct (sqex_exact_access_frame with "Hstate Hl Hothers") as %Hframe;
      [exact Hnames | exact Hvalid |].
    iMod (sqex_state_write with "Hstate Hl") as "[Hstate Hl]"; [done | done |].
    iEval (rewrite -(sqex_exact_threads_inv_write_frame _ _ _ _ _ _ vn Hframe
      (ex_intro _ (LitV (LitInt cur)) Hm))) in "Hothers".
    iModIntro. iNext.
    iMod ("Hcont" $! (Some (LitV (LitInt 1))) with "[Hl]") as "Hwp".
    { simpl. rewrite bool_decide_true // decide_True //. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma sqex_external_cas_fail_pending E C tp m p hF mu i e k l ve vn old Φ :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> sq_freeable_rel m hF ->
    ✓ sq_heap_cells m p -> sqex_pool_matches C tp -> sqex_pool_reservations tp m mu ->
    tp !! i = Some (Running e []) -> lr_external e (ACAS tt l ve vn) k ->
    m !! l = Some old -> lr_val_neq m old ve ->
    uPred_ownM (sqex_state_resource m p hF) -∗ EXWP e @ E {{ Φ }} -∗
    sqex_exact_threads_inv m hF (delete i C) ={E,∅}=∗
      ▷ |={∅,E}=> uPred_ownM (sqex_state_resource m p hF) ∗
        EXWP k (Some (LitV (LitInt 0))) @ E {{ Φ }} ∗
        sqex_exact_threads_inv m hF (delete i C).
  Proof.
    intros Hnames Hrel HFrel Hvalid Hmatch Hres Hi He Hload Hneq.
    iIntros "Hstate Hwp Hothers". rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod "Hwp" as ([cur expected]) "[[%Hexpected Hl] Hcont]". simpl in Hexpected.
    iDestruct (sqex_state_lookup with "Hstate Hl") as %[Hm _]; [done | done |].
    simpl in Hm. have Hold : old = LitV (LitInt cur) by congruence.
    have Hdifferent : cur ≠ expected.
    { rewrite Hold Hexpected /lr_val_neq in Hneq. inversion Hneq. congruence. }
    iModIntro. iNext.
    iMod ("Hcont" $! (Some (LitV (LitInt 0))) with "[Hl]") as "Hwp".
    { simpl. rewrite bool_decide_false // decide_False //. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma sqex_external_cas_writable E C tp m p hF mu i e k l ve vn Φ :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p -> sq_freeable_rel m hF ->
    ✓ sq_heap_cells m p -> sqex_pool_matches C tp -> sqex_pool_reservations tp m mu ->
    tp !! i = Some (Running e []) -> lr_external e (ACAS tt l ve vn) k ->
    uPred_ownM (sqex_state_resource m p hF) -∗ EXWP e @ E {{ Φ }} -∗
    sqex_exact_threads_inv m hF (delete i C) ={E,∅}=∗ ⌜mu !! l = Some (Rst 0)⌝.
  Proof.
    intros Hnames Hrel HFrel Hvalid Hmatch Hres Hi He.
    iIntros "Hstate Hwp Hothers". rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod "Hwp" as ([cur expected]) "[[_ Hl] _]".
    iDestruct (sqex_state_lookup with "Hstate Hl") as %[Hm _]; [done | done |].
    iDestruct (sqex_exact_access_frame with "Hstate Hl Hothers") as %Hframe;
      [exact Hnames | exact Hvalid |].
    iModIntro. iPureIntro.
    exact (sqex_access_frame_writable _ _ _ _ _ _ _ _
      Hframe Hmatch Hres Hi (ex_intro _ (LitV (LitInt cur)) Hm)).
  Qed.

  Lemma sqex_external_spawn_pending E C tp m p hF mu i e k child j Φ :
    tp !! i = Some (Running e []) -> lr_external e (ASpawn child) k ->
    tp !! j = None -> (forall n, n < j -> is_Some (tp !! n)) ->
    uPred_ownM (sqex_state_resource m p hF) -∗ EXWP e @ E {{ Φ }} -∗
    sqex_exact_threads_inv m hF (delete i C) ={E,∅}=∗
      ⌜at_step (AMCfg tp m mu)
        (AMCfg (<[j := Running child []]> (<[i := Running (k None) []]> tp)) m mu)⌝ ∗
      ▷ |={∅,E}=> uPred_ownM (sqex_state_resource m p hF) ∗
        EXWP k None @ E {{ Φ }} ∗ EXWP child {{ _, True }} ∗
        sqex_exact_threads_inv m hF (delete i C).
  Proof.
    intros Hi He Hfresh Hleast. iIntros "Hstate Hwp Hothers".
    rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod "Hwp" as ([]) "[Hchild Hcont]". simpl.
    iModIntro. iSplit.
    { iPureIntro. by eapply (Spawn (L := lr_language)) with (e_new := child). }
    iNext. iMod ("Hcont" $! None with "[]") as "Hwp"; first done.
    iModIntro. by iFrame.
  Qed.
End external_steps.
