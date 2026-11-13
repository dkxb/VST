(** Logical sequential steps retain exact per-thread permission resources. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_later.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_perm.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_pool_resources.
Require Import VST.atomic_machine.lambda_rust.equivalence.
From iris.algebra Require Import big_op gmap.

Set Default Proof Using "Type".
Local Existing Instance lr_ext_specs.

Lemma sqex_coherent_member_included {Σ} m p (C : sqex_threads Σ) i c :
  sqex_threads_coherent m p C -> C !! i = Some c ->
  sq_heap_cells m (sqex_thread_perm c) ≼ sq_heap_cells m p.
Proof.
  intros (_ & _ & Hsum & _) Hi.
  rewrite /sqex_threads_cells (big_opM_delete _ C i c Hi) in Hsum.
  etrans; [apply cmra_included_l | exact Hsum].
Qed.

Section sequential_step.
  Context `{!lrSqGS Σ}.

  Lemma sqex_exact_seq_step m total hF c T e' m' :
    sq_heap_name ≠ sq_freeable_name ->
    sq_heap_rel m total -> sq_heap_rel m (sqex_thread_perm c) ->
    sq_freeable_rel m hF ->
    sq_heap_cells m (sqex_thread_perm c) ≼ sq_heap_cells m total ->
    lr_step (sqex_thread_expr c) m T e' m' ->
    uPred_ownM (sqex_state_resource m total hF) -∗
    sqex_exact_thread_inv m hF c ==∗ ▷ |==>
    ∃ total' hF',
      ⌜perm_step T total total' ∧
        perm_step T (sqex_thread_perm c) (sqex_perm_after T (sqex_thread_perm c)) ∧
        sq_heap_rel m' total' ∧ sq_freeable_rel m' hF'⌝ ∗
      uPred_ownM (sqex_state_resource m' total' hF') ∗
      sqex_exact_thread_inv m' hF'
        (SqexThread e' (sqex_perm_after T (sqex_thread_perm c)) (sqex_thread_post c)).
  Proof.
    intros Hnames Htotalrel Hlocalrel HFrel [f Hframe] Hstep.
    have Heffect := lr_step_mem_effect _ _ _ _ _ Hstep.
    iIntros "Hstate Hthread".
    iDestruct (sqex_exact_thread_permissions _ _ _ Hlocalrel HFrel
      with "Hthread") as "#Hpermissions".
    iPoseProof ("Hpermissions" $! T e' m' with "[%]") as "#Hlocal"; first done.
    iAssert (▷ ⌜perm_step T (sqex_thread_perm c)
      (sqex_perm_after T (sqex_thread_perm c))⌝)%I as "#Hlocal_after".
    { iNext. iDestruct "Hlocal" as %(local' & Hlocal).
      iPureIntro. by eapply sqex_perm_step_after. }
    iDestruct "Hthread" as (r) "(Hr & #Hsupport & %Hexact & #Hfits)".
    iDestruct (sqex_exact_fragment_only _ _ _ _ Hexact with "Hfits") as %Hfragment.
    set (R := (EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }} ∗
      ▷ ⌜perm_step T (sqex_thread_perm c)
          (sqex_perm_after T (sqex_thread_perm c))⌝)%I).
    iAssert (sqex_support R r) as "#Hsupport_all".
    { rewrite /sqex_support /R. iIntros "!> Hr". iSplitL "Hr"; last done.
      by iApply ("Hsupport" with "Hr"). }
    set (I := { z : perm_map * sq_freeableUR |
      perm_step T total z.1 ∧
      perm_step T (sqex_thread_perm c) (sqex_perm_after T (sqex_thread_perm c)) ∧
      sq_heap_rel m' z.1 ∧ sq_freeable_rel m' z.2 }).
    set (Sout := fun z : I =>
      (sqex_state_resource m' (proj1_sig z).1 (proj1_sig z).2 : iResUR Σ)).
    set (Aout := fun z : I => sq_heap_cells m' (proj1_sig z).1).
    set (Bout := fun _ : I =>
      sq_heap_cells m' (sqex_perm_after T (sqex_thread_perm c))).
    set (Qout := fun _ : I => (EXWP e' {{ v, sqex_thread_post c v }})%I).
    have HSout : forall z, @sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name
      (Sout z) ≡ Some (● Aout z).
    { intros z. exact (sqex_state_heap_project m' (proj1_sig z).1 (proj1_sig z).2 Hnames). }
    assert (Hexecute : uPred_ownM (sqex_state_resource m total hF) ∗ R ⊢
      |==> ▷ |==> sqex_state_update_post (sq_heap_cells m total)
        (sq_heap_cells m (sqex_thread_perm c)) Sout Aout Bout Qout).
    { iIntros "[Hstate [Hwp Hlocal]]".
      rewrite (exwp_seq_unfold _ _ _ (lr_step_not_value _ _ _ _ _ Hstep)
        (lr_step_not_external _ _ _ _ _ Hstep)).
      iMod ("Hwp" with "[Hstate]") as "[_ Hcontinue]".
      { by iApply (sqex_state_resource_heap _ _ _ Htotalrel HFrel with "Hstate"). }
      iPoseProof ("Hcontinue" $! T e' m' with "[%]") as "Hcontinue"; first done.
      iModIntro. iNext. iDestruct "Hlocal" as %Hlocal.
      iMod "Hcontinue" as (total') "(%Hglobal & Hheap & Hwp)".
      iDestruct "Hheap" as (hF') "(Hm & HF & %Hrels)".
      destruct Hrels as [Hrel' HFrel'].
      iModIntro. iExists (exist _ (total', hF') (conj Hglobal (conj Hlocal (conj Hrel' HFrel')))).
      iSplit.
      { iPureIntro. by eapply sqex_seq_cells_local_update. }
      iSplitL "Hm HF".
      { rewrite /Sout /= sqex_state_resource_own. by iFrame. }
      done. }
    iMod (@sqex_bupd_later_state_retain_fragment Σ sq_heapUR sq_heap_inG _
      sqex_heap_cancelable I sq_heap_name (sq_heap_cells m total)
      (sq_heap_cells m (sqex_thread_perm c)) f (sqex_state_resource m total hF) r
      Sout Aout Bout R Qout (sqex_state_heap_project _ _ _ Hnames)
      Hfragment Hframe HSout Hexecute with "[$Hstate $Hr $Hsupport_all]") as "Hnext".
    iModIntro. iNext. iMod "Hnext" as (z r') "(Hstate & Hr & #Hsupport_next & %Hproject)".
    destruct z as [[total' hF'] (Hglobal & Hlocal & Hrel' & HFrel')].
    iEval (rewrite /Sout /=) in "Hstate".
    iEval (rewrite /Qout /=) in "Hsupport_next".
    have Hlocalrel' : sq_heap_rel m' (sqex_perm_after T (sqex_thread_perm c)).
    { by eapply sqex_seq_heap_rel. }
    have Hexact' : sq_heap_cells m' (sqex_perm_after T (sqex_thread_perm c)) ≡
        sqex_heap_fragment r'.
    { apply sqex_heap_projection_exact. exact Hproject. }
    iDestruct (sqex_exact_witness_intro _ _ _ _ _ _ _ Hnames Hlocalrel' Hexact'
      with "Hstate Hr Hsupport_next") as "[Hstate Hthread]".
    iModIntro. iExists total', hF'. by iFrame.
  Qed.

  Lemma sqex_exact_pool_seq_step m total hF C i c T e' m' :
    sq_heap_name ≠ sq_freeable_name ->
    sqex_threads_coherent m total C -> sq_freeable_rel m hF -> C !! i = Some c ->
    lr_step (sqex_thread_expr c) m T e' m' ->
    uPred_ownM (sqex_state_resource m total hF) -∗
    sqex_exact_thread_inv m hF c -∗ sqex_exact_threads_inv m hF (delete i C) ==∗
    ▷ |==> ∃ total' local' hF',
      ⌜perm_step T total total' ∧ perm_step T (sqex_thread_perm c) local' ∧
        sq_freeable_rel m' hF' ∧
        sqex_threads_coherent m' total'
          (<[i := SqexThread e' local' (sqex_thread_post c)]> C)⌝ ∗
      uPred_ownM (sqex_state_resource m' total' hF') ∗
      sqex_exact_thread_inv m' hF' (SqexThread e' local' (sqex_thread_post c)) ∗
      sqex_exact_threads_inv m' hF' (delete i C).
  Proof.
    intros Hnames Hcoherent HFrel Hi Hstep. iIntros "Hstate Hthread Hothers".
    have Hlocalrel := proj2 (proj2 (proj2 Hcoherent)) _ _ Hi.
    have Hin := sqex_coherent_member_included _ _ _ _ _ Hcoherent Hi.
    iMod (sqex_exact_seq_step _ _ _ _ _ _ _ Hnames (proj1 Hcoherent)
      Hlocalrel HFrel Hin Hstep with "Hstate Hthread") as "Hnext".
    iModIntro. iNext.
    iMod "Hnext" as (total' hF') "(%Hresult & Hstate & Hthread)".
    destruct Hresult as (Hglobal & Hlocal & Hrel' & HFrel').
    have Hframe : forall j d, delete i C !! j = Some d ->
      sq_heap_rel m' (sqex_thread_perm d) ∧
      sq_heap_cells m' (sqex_thread_perm d) ≡ sq_heap_cells m (sqex_thread_perm d).
    { intros j d Hj. apply (lookup_delete_Some (M := gmap nat)) in Hj as [Hne Hj].
      destruct (sqex_seq_frame _ _ _ _ _ (sqex_thread_perm d)
        (lr_step_mem_effect _ _ _ _ _ Hstep) Hlocal
        (proj2 (proj2 (proj2 Hcoherent)) _ _ Hj)) as [Hcells Hrel].
      - by eapply sqex_threads_pair_valid.
      - split; first done. by rewrite Hcells. }
    iDestruct (sqex_exact_threads_transport _ _ _ _ _ _ Hnames Hframe
      with "Hstate Hothers") as "[Hstate Hothers]".
    iModIntro. iExists total', (sqex_perm_after T (sqex_thread_perm c)), hF'. iFrame.
    iPureIntro. split; first exact Hglobal. split; first exact Hlocal.
    split; first exact HFrel'.
    by eapply sqex_threads_coherent_seq.
  Qed.
End sequential_step.
