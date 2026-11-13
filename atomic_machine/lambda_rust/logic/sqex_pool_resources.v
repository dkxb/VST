(** Logical resource lemmas for a pool with exact thread permission maps. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_resource_split.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pool_steps.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
From iris.algebra Require Import auth gmap agree.

Set Default Proof Using "Type".
Local Existing Instance lr_ext_specs.

Section pool_resources.
  Context `{!lrSqGS Σ}.

  Lemma sqex_exact_thread_wp m hF c :
    sqex_exact_thread_inv m hF c -∗
    EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}.
  Proof.
    iIntros "Hthread". iApply sqex_thread_inv_wp.
    by iApply sqex_exact_thread_inv_forget.
  Qed.

  Lemma sqex_exact_thread_permissions m hF c :
    sq_heap_rel m (sqex_thread_perm c) -> sq_freeable_rel m hF ->
    sqex_exact_thread_inv m hF c -∗
    ∀ T e' m', ⌜lr_step (sqex_thread_expr c) m T e' m'⌝ -∗
      ▷ ⌜exists p', perm_step T (sqex_thread_perm c) p'⌝.
  Proof.
    intros Hrel HFrel. iIntros "Hthread" (T e' m' Hstep).
    iApply (sqex_thread_inv_permissions _ _ _ _ _ _ Hrel HFrel Hstep).
    by iApply sqex_exact_thread_inv_forget.
  Qed.

  Lemma sqex_exact_thread_transport m hF m' p' hF' c :
    sq_heap_name ≠ sq_freeable_name ->
    sq_heap_rel m' (sqex_thread_perm c) ->
    sq_heap_cells m' (sqex_thread_perm c) ≡ sq_heap_cells m (sqex_thread_perm c) ->
    uPred_ownM (sqex_state_resource m' p' hF') -∗ sqex_exact_thread_inv m hF c -∗
    uPred_ownM (sqex_state_resource m' p' hF') ∗ sqex_exact_thread_inv m' hF' c.
  Proof.
    intros Hnames Hrel Hcells. iIntros "Hstate (%r & Hr & Hsupport & %Hexact & _)".
    iDestruct (sqex_resource_fits_intro with "Hstate Hr") as "#Hvalid".
    iDestruct (sqex_state_projection _ _ _ _ Hnames with "Hvalid") as "[_ Hfits]".
    have Hperm : sqex_thread_perm c = sqex_resource_permissions r.
    { apply (sqex_resource_permissions_exact m'); [done | by rewrite Hcells]. }
    iFrame "Hstate". iExists r. iFrame "Hr Hsupport". iSplit.
    - iPureIntro. by rewrite Hcells.
    - by rewrite Hperm.
  Qed.

  Lemma sqex_exact_threads_transport m hF m' p' hF' (C : sqex_threads Σ) :
    sq_heap_name ≠ sq_freeable_name ->
    (forall i c, C !! i = Some c ->
      sq_heap_rel m' (sqex_thread_perm c) ∧
      sq_heap_cells m' (sqex_thread_perm c) ≡ sq_heap_cells m (sqex_thread_perm c)) ->
    uPred_ownM (sqex_state_resource m' p' hF') -∗ sqex_exact_threads_inv m hF C -∗
    uPred_ownM (sqex_state_resource m' p' hF') ∗ sqex_exact_threads_inv m' hF' C.
  Proof.
    intros Hnames. unfold sqex_threads in C.
    induction C as [|i c C Hfresh IH] using map_ind; intros Hcells.
    - rewrite /sqex_exact_threads_inv !big_sepM_empty. iIntros "Hstate _". by iFrame.
    - rewrite /sqex_exact_threads_inv !big_sepM_insert //.
      iIntros "Hstate [Hthread Hothers]".
      have Hci : (<[i := c]> C) !! i = Some c by apply (lookup_insert_eq (M := gmap nat)).
      have Hc := Hcells i c Hci.
      have Hothers : forall j d, C !! j = Some d ->
          sq_heap_rel m' (sqex_thread_perm d) ∧
          sq_heap_cells m' (sqex_thread_perm d) ≡ sq_heap_cells m (sqex_thread_perm d).
      { intros j d Hd. apply (Hcells j d). rewrite lookup_insert_ne; first done.
        intros ->. congruence. }
      iDestruct (sqex_exact_thread_transport _ _ _ _ _ _ Hnames (proj1 Hc) (proj2 Hc)
        with "Hstate Hthread") as "[Hstate Hthread]".
      iDestruct (IH Hothers with "Hstate Hothers") as "[Hstate Hothers]".
      by iFrame.
  Qed.

  Lemma sqex_heap_fragment_own_fragment h :
    sqex_heap_fragment (own.iRes_singleton sq_heap_name (◯ h)) ≡ h.
  Proof. by rewrite /sqex_heap_fragment sqex_project_singleton. Qed.

  Lemma sqex_exact_thread_access_valid m p hF c l q v :
    sq_heap_name ≠ sq_freeable_name -> ✓ sq_heap_cells m p ->
    uPred_ownM (sqex_state_resource m p hF) -∗ l ↦{q} v -∗
    sqex_exact_thread_inv m hF c -∗
    ⌜✓ ({[l := (q, to_agree v)]} ⋅ sq_heap_cells m (sqex_thread_perm c))⌝.
  Proof.
    intros Hnames Hvalid. iIntros "Hstate Hl (%r & Hr & Hsupport & %Hcells & Hfits)".
    iAssert (uPred_ownM (sqex_state_resource m p hF ⋅
      (own.iRes_singleton sq_heap_name (◯ {[l := (q, to_agree v)]}) ⋅ r)))
      with "[Hstate Hl Hr]" as "Hown".
    { rewrite !uPred.ownM_op. iFrame "Hstate Hr".
      by iEval (rewrite /sq_pointsto own.own_eq) in "Hl". }
    iDestruct (uPred.ownM_valid with "Hown") as "#Hvalid".
    iDestruct (sqex_state_projection _ _ _ _ Hnames with "Hvalid") as "[%Hprojection _]".
    iPureIntro. eapply cmra_valid_included; first exact Hvalid.
    rewrite Hcells -(sqex_heap_fragment_own_fragment {[l := (q, to_agree v)]})
      -sqex_heap_fragment_op.
    exact (proj2 (proj2 Hprojection)).
  Qed.

  Lemma sqex_exact_access_frame m p hF C i l q v :
    sq_heap_name ≠ sq_freeable_name -> ✓ sq_heap_cells m p ->
    uPred_ownM (sqex_state_resource m p hF) -∗ l ↦{q} v -∗
    sqex_exact_threads_inv m hF (delete i C) -∗
    ⌜sqex_access_frame m C i l q v⌝.
  Proof.
    intros Hnames Hvalid. iIntros "Hstate Hl Hothers".
    iApply pure_forall_2. iIntros (j). iApply pure_forall_2. iIntros (c).
    rewrite !bi.pure_impl. iIntros (Hne Hc).
    have Hj : delete i C !! j = Some c by rewrite lookup_delete_ne; last congruence.
    iDestruct (big_sepM_lookup _ _ _ _ Hj with "Hothers") as "Hthread".
    by iApply (sqex_exact_thread_access_valid with "Hstate Hl Hthread").
  Qed.

  Lemma sqex_ready_progress m p hF C tp mu i c :
    sq_heap_name ≠ sq_freeable_name -> sqex_threads_coherent m p C ->
    sq_freeable_rel m hF -> sqex_pool_matches C tp ->
    sqex_pool_reservations tp m mu -> C !! i = Some c ->
    tp !! i = Some (Running (sqex_thread_expr c) []) ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    sqex_exact_threads_inv m hF C ={⊤,∅}=∗
      ▷ ⌜am_not_stuck (Running (sqex_thread_expr c) []) m mu⌝.
  Proof.
    intros Hnames Hcoherent HFrel Hmatch Hres Hc Hi.
    have Hrel := proj1 Hcoherent.
    have Hvalid := proj1 (proj2 Hcoherent).
    iIntros "Hstate Hthreads".
    iDestruct (big_sepM_delete _ _ _ _ Hc with "Hthreads") as "[Hthread Hothers]".
    iDestruct (sqex_exact_thread_permissions _ _ _
      (proj2 (proj2 (proj2 Hcoherent)) _ _ Hc) HFrel with "Hthread") as "#Hpermissions".
    iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
    destruct (to_val (sqex_thread_expr c)) as [v|] eqn:Hv.
    { iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
      iModIntro. iNext. iPureIntro. left. exists (sqex_thread_expr c).
      split; first done. by exists v. }
    iEval (rewrite exwp_unfold /exwp_pre Hv) in "Hwp".
    iMod "Hwp" as "[[_ Hseq] | (%op & %k & %Hcall & Hspec)]".
    - iMod ("Hseq" with "[Hstate]") as "[%Hred _]".
      { by iApply (sqex_state_resource_heap _ _ _ Hrel HFrel with "Hstate"). }
      destruct Hred as (T & e' & m' & Hstep).
      destruct (sqex_step_fresh_reservations _ _ _ _ _ mu Hstep)
        as (T' & e'' & m'' & Hstep' & Halloc).
      iPoseProof ("Hpermissions" $! T' e'' m'' with "[%]") as "Hperm"; first done.
      iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
      iModIntro. iNext. iDestruct "Hperm" as %(local' & Hperm).
      iPureIntro. right.
      destruct (sqex_ready_step_reservable _ _ _ _ _ _ _ _ _ _ _ _
        Hcoherent Hmatch Hres Hc Hi Hstep' Hperm Halloc) as [mu' Hrsv].
      eexists. eapply Core_Try; [apply (lookup_singleton_eq (M := gmap nat)) | exact Hstep' | exact Hrsv].
    - iMod "Hspec" as (x) "[Hpre _]".
      destruct op as [ly l|ly l v|ly l ve vn|child].
      + destruct ly, x as [q v].
        iDestruct (sq_heap_gen_read with "[Hstate] Hpre") as %Hm.
        { by iApply (sqex_state_resource_heap _ _ _ Hrel HFrel with "Hstate"). }
        iDestruct (sqex_exact_access_frame _ _ _ _ _ _ _ _ Hnames Hvalid
          with "Hstate Hpre Hothers") as %Hframe.
        destruct (sqex_access_frame_readable _ _ _ _ _ _ _ _ _
          Hframe Hmatch Hres Hi ltac:(by exists v)) as [n Hmu].
        iModIntro. iNext. iPureIntro. right. eexists.
        eapply SC_Read; [apply (lookup_singleton_eq (M := gmap nat)) | exact Hcall | | exact Hm].
        apply Forall_singleton. by rewrite Hmu.
      + destruct ly.
        iDestruct (sq_heap_gen_read with "[Hstate] Hpre") as %Hm.
        { by iApply (sqex_state_resource_heap _ _ _ Hrel HFrel with "Hstate"). }
        iDestruct (sqex_exact_access_frame _ _ _ _ _ _ _ _ Hnames Hvalid
          with "Hstate Hpre Hothers") as %Hframe.
        have Hmu := sqex_access_frame_writable _ _ _ _ _ _ _ _
          Hframe Hmatch Hres Hi ltac:(by exists x).
        iModIntro. iNext. iPureIntro. right. eexists.
        eapply SC_Write; [apply (lookup_singleton_eq (M := gmap nat)) | exact Hcall | | ].
        * by apply Forall_singleton.
        * by rewrite /= Hm.
      + destruct ly, x as [cur expected].
        iDestruct "Hpre" as "[%Hexpected Hl]". simpl in Hexpected.
        iDestruct (sq_heap_gen_read with "[Hstate] Hl") as %Hm.
        { by iApply (sqex_state_resource_heap _ _ _ Hrel HFrel with "Hstate"). }
        iDestruct (sqex_exact_access_frame _ _ _ _ _ _ _ _ Hnames Hvalid
          with "Hstate Hl Hothers") as %Hframe.
        have Hmu := sqex_access_frame_writable _ _ _ _ _ _ _ _
          Hframe Hmatch Hres Hi ltac:(by exists (LitV (LitInt cur))).
        subst ve. iModIntro. iNext. iPureIntro. right.
        destruct (decide (cur = expected)) as [->|Hne]; eexists.
        * eapply SC_Cas_Suc; [apply (lookup_singleton_eq (M := gmap nat))
            | exact Hcall | | exact Hm | | ].
          -- by apply Forall_singleton.
          -- simpl. constructor.
          -- by rewrite /= Hm.
        * eapply SC_Cas_Fail; [apply (lookup_singleton_eq (M := gmap nat))
            | exact Hcall | | exact Hm | ].
          -- apply Forall_singleton. by rewrite Hmu.
          -- simpl. constructor. congruence.
      + destruct (tpool_least_free {[0%nat := Running (sqex_thread_expr c) []]})
          as (j & Hj & Hleast).
        iModIntro. iNext. iPureIntro. right. eexists.
        eapply Spawn; [apply (lookup_singleton_eq (M := gmap nat)) | exact Hcall | exact Hj | exact Hleast].
  Qed.
End pool_resources.
