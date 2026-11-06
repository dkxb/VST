(** Compositional rules for EXWP. External calls and spawning admit fancy updates. *)
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.at_logic.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Set Default Proof Using "Type".
Local Existing Instance lrSqGS_invGS.

Lemma lr_external_det e op1 k1 op2 k2 :
  lr_external e op1 k1 -> lr_external e op2 k2 ->
  op2 = op1 /\ forall ov, k2 ov = k1 ov.
Proof.
  intros H1 H2. destruct H1 as [K1 e1 op1 k1 H1].
  inversion H2 as [K2 e2 op2x k2x Hh Heq]; subst.
  destruct (fill_redex_unique K2 K1 e2 e1
    (lr_head_external_redex_shape _ _ _ Hh)
    (lr_head_external_redex_shape _ _ _ H1)
    (lr_head_external_not_val _ _ _ Hh)
    (lr_head_external_not_val _ _ _ H1) Heq) as [-> ->].
  destruct H1; inversion Hh; subst; split; congruence.
Qed.

Lemma lr_external_fill K e op k :
  lr_external e op k -> exists k',
    lr_external (fill K e) op k' /\ forall ov, k' ov = fill K (k ov).
Proof.
  intros H. destruct H as [K' e op k Hh].
  exists (fun ov => fill (K' ++ K) (k ov)).
  rewrite -fill_app. split; [by constructor | intro ov; by rewrite fill_app].
Qed.

Section semantics.
  Context `{!ExtCallSems lr_language}.

  (** Return from a request uses the continuation exposed by [lr_external]. *)
  Lemma ext_step_call_inv e m e' m' efs :
    ext_step (L := lr_language) e m e' m' efs ->
    exists op k ov, lr_external e op k /\
      extcall_sems op m ov m' efs /\ e' = k ov.
  Proof.
    intros Hstep. destruct Hstep as [e op k m ov m' e' efs He Hsem Ha].
    destruct Ha as [e op' k' ov He'].
    destruct (lr_external_det _ _ _ _ _ He' He) as [-> _].
    exists op', k', ov. auto.
  Qed.

  Lemma ext_step_inv e op k m e' m' efs :
    lr_external e op k -> ext_step (L := lr_language) e m e' m' efs ->
    exists ov, extcall_sems op m ov m' efs /\ e' = k ov.
  Proof.
    intros He Hstep.
    destruct (ext_step_call_inv _ _ _ _ _ Hstep) as (op' & k' & ov & He' & Hsem & ->).
    destruct (lr_external_det _ _ _ _ _ He He') as [-> Hk].
    exists ov. split; [done | apply Hk].
  Qed.

  Lemma ext_step_fill K e m e' m' efs :
    ext_step (L := lr_language) e m e' m' efs ->
    ext_step (L := lr_language) (fill K e) m (fill K e') m' efs.
  Proof.
    intros Hstep.
    destruct (ext_step_call_inv _ _ _ _ _ Hstep) as (op & k & ov & He & Hsem & ->).
    destruct (lr_external_fill K _ _ _ He) as (k' & He' & Hk).
    eapply ExtStep; [exact He' | exact Hsem | ].
    rewrite -(Hk ov). by econstructor.
  Qed.

  Lemma ext_step_fill_inv K e m e' m' efs :
    to_val e = None -> ext_step (L := lr_language) (fill K e) m e' m' efs ->
    exists e2, e' = fill K e2 /\ ext_step (L := lr_language) e m e2 m' efs.
  Proof.
    intros Hv Hstep.
    destruct (ext_step_call_inv _ _ _ _ _ Hstep) as (op & k & ov & He & Hsem & ->).
    inversion He as [K' r op' k' Hh Heq]; subst.
    destruct (fill_decompose K K' e r (lr_head_external_redex_shape _ _ _ Hh)
      (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
    exists (fill K'' (k' ov)). rewrite fill_app. split; [done | ].
    eapply ExtStep; [by constructor | exact Hsem | ].
    apply (LRAfterExternal _ op (fun ov => fill K'' (k' ov))). by constructor.
  Qed.
End semantics.

Section rules.
  Context `{!ExtCallSems lr_language, !lrSqGS Σ}.

  Lemma bupd_exwp E e Φ : (|==> EXWP e @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof.
    rewrite exwp_unfold /exwp_pre. destruct (to_val e); apply bupd_trans.
  Qed.

  Lemma exwp_value E v Φ : Φ v ⊢ EXWP of_val v @ E {{ Φ }}.
  Proof. rewrite exwp_value_bupd. apply bupd_intro. Qed.

  Lemma exwp_bind K E e Φ :
    EXWP e @ E {{ v, EXWP fill K (of_val v) @ E {{ Φ }} }} ⊢
    EXWP fill K e @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e). rewrite (exwp_unfold E e) /exwp_pre.
    destruct (to_val e) as [v|] eqn:Hv.
    { apply of_to_val in Hv. subst e. iApply bupd_exwp. }
    rewrite exwp_unfold /exwp_pre (fill_not_val _ _ Hv).
    iIntros ">[Hseq | [%Hext Hext]] !>".
    - iLeft. iIntros (m) "Hm". iMod ("Hseq" with "Hm") as "[%Hr Hstep]".
      iModIntro. iSplit.
      { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
        exists T, (fill K e2), m2. destruct Hs. rewrite -!fill_app. by constructor. }
      iIntros (T e2 m2 Hs).
      inversion Hs as [K' r m0 T0 r' m0' Hh Heq]; subst.
      destruct (fill_decompose K K' e r (lr_head_step_redex_shape _ _ _ _ _ Hh)
        (lr_head_step_not_val _ _ _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
      iDestruct ("Hstep" $! T (fill K'' r') m2 with "[%]") as "Hstep".
      { by constructor. }
      iNext. iMod "Hstep" as "[$ Hwp]". iModIntro. rewrite fill_app. by iApply "IH".
    - iRight. iSplit.
      { iPureIntro. destruct Hext as (op & k & Hext).
        destruct (lr_external_fill K _ _ _ Hext) as (k' & H & _). eauto. }
      iIntros (m) "Hm". iMod ("Hext" with "Hm") as "[%Hr Hstep]".
      iModIntro. iSplit.
      { iPureIntro. destruct Hr as (e2 & m2 & efs & Hs). eauto using ext_step_fill. }
      iIntros (e2 m2 efs Hs).
      destruct (ext_step_fill_inv _ _ _ _ _ _ Hv Hs) as (e' & -> & Hs').
      iMod ("Hstep" $! e' m2 efs with "[%]") as "Hstep"; first done.
      iModIntro. iNext. iMod "Hstep" as "Hstep". iModIntro.
      iMod "Hstep" as "[$ [Hwp $]]". iModIntro. by iApply "IH".
  Qed.

  Lemma exwp_ext_unfold E e op k Φ :
    lr_external e op k ->
    EXWP e @ E {{ Φ }} ⊣⊢
      (∀ m1, sq_heap m1 ={E,∅}=∗
        ⌜exists e2 m2 efs, ext_step (L := lr_language) e m1 e2 m2 efs⌝ ∗
        ∀ e2 m2 efs, ⌜ext_step (L := lr_language) e m1 e2 m2 efs⌝ -∗
          |={∅}▷=> |={∅,E}=> sq_heap m2 ∗ EXWP e2 @ E {{ Φ }} ∗
            [∗ list] ef ∈ efs, EXWP ef {{ _, True }}).
  Proof.
    intros He. iSplit; last by iApply (exwp_lift_ext_step _ _ _ _ _ He).
    rewrite exwp_unfold /exwp_pre (lr_external_not_val _ _ _ He).
    iIntros "H" (m) "Hm". iMod "H" as "[Hseq | [_ Hext]]".
    - iMod ("Hseq" with "Hm") as "[%Hr _]".
      destruct Hr as (T & e2 & m2 & Hs). exfalso.
      exact (lr_step_external_disjoint _ _ _ _ _ _ _ Hs He).
    - by iApply "Hext".
  Qed.

  Lemma exwp_stuck E Φ m :
    sq_heap m -∗ EXWP stuck_term @ E {{ Φ }} ==∗ False.
  Proof.
    assert (Hr : redex_shape stuck_term).
    { unfold stuck_term. intros Ki e He; destruct Ki; simpl in He;
        simplify_eq; eauto; discriminate_list. }
    rewrite exwp_seq_unfold; [ | done | ].
    - iIntros "Hm Hwp". iMod ("Hwp" with "Hm") as "[%Hs _]".
      destruct Hs as (T & e2 & m2 & Hs). apply lr_step_head in Hs; [inversion Hs | done].
    - intros op k He. apply lr_external_head in He; [inversion He | done].
  Qed.

  (** This rule grants invariant access around an external call.
      A failed external return may be [stuck_term], which EXWP excludes. *)
  Lemma exwp_atomic_ext E1 E2 e op k Φ :
    lr_external e op k ->
    (forall m e2 m2 efs, ext_step (L := lr_language) e m e2 m2 efs ->
      is_Some (to_val e2) \/ e2 = stuck_term) ->
    (|={E1,E2}=> EXWP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
      EXWP e @ E1 {{ Φ }}.
  Proof.
    intros He Ha. iIntros "Hwp".
    iApply (exwp_lift_ext_step _ _ _ _ _ He).
    iIntros (m) "Hm". iMod "Hwp" as "Hwp".
    rewrite (exwp_ext_unfold _ _ _ _ _ He).
    iMod ("Hwp" with "Hm") as "[$ Hstep]". iModIntro.
    iIntros (e2 m2 efs Hs).
    iMod ("Hstep" $! e2 m2 efs with "[%]") as "Hstep"; first done.
    iModIntro. iNext. iMod "Hstep" as "Hstep". iModIntro.
    iMod "Hstep" as "[Hm [Hwp Hforks]]".
    destruct (Ha _ _ _ _ Hs) as [[v Hv] | ->].
    - apply of_to_val in Hv as <-. rewrite exwp_value_bupd.
      iMod "Hwp" as ">Hpost". iModIntro. iFrame. by iApply exwp_value.
    - iMod (exwp_stuck with "Hm Hwp") as %[].
  Qed.

  Lemma exwp_pure_step E e1 e2 Φ :
    @pure_step sq_lang e1 e2 ->
    ▷ EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    intros [Hsafe Hdet].
    assert (Hv : to_val e1 = None).
    { destruct (Hsafe ∅) as (e' & m' & efs & Hs). exact (language.val_stuck _ _ _ _ _ _ Hs). }
    iIntros "Hwp". iApply exwp_lift_step; first done.
    iIntros (m) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (Hsafe m) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      eauto. }
    iIntros (T e' m' Hs).
    destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
    { by apply sq_prim_step_lr_step. }
    iNext. by iFrame.
  Qed.

  Lemma exwp_pure_steps E e1 e2 Φ n :
    nsteps (@pure_step sq_lang) n e1 e2 ->
    ▷^n EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    induction 1 as [e | n e1 e2 e3 Hs Hsteps IH]; first done.
    simpl. iIntros "H". iApply (exwp_pure_step _ _ _ _ Hs).
    iNext. by iApply IH.
  Qed.

  Lemma exwp_alloc E Φ :
    (▷ ∀ l, l ↦ LitV LitPoison -∗ Φ (LitV (LitLoc l))) -∗
    EXWP (Alloc (Lit (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply exwp_lift_step; first done.
    iIntros (m) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
      do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext.
    iMod (sq_heap_alloc _ _ 1 with "Hm") as "[Hm [_ Hl]]"; [lia | done | ].
    rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
    iModIntro. iFrame. iApply (exwp_value _ (LitV (LitLoc l))). by iApply "HΦ".
  Qed.
End rules.

Section sc_rules.
  Context `{!ExtCallSems lr_language, !lrSqGS Σ}.

  Lemma exwp_read_sc_atomic E1 E2 l Φ :
    (|={E1,E2}=> EXWP (Read ScOrd (Lit (LitLoc l))) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (Read ScOrd (Lit (LitLoc l))) @ E1 {{ Φ }}.
  Proof.
    assert (He : lr_external (Read ScOrd (Lit (LitLoc l))) (ALoad tt l) lr_result_expr).
    { apply (LREctxExternal []). constructor. }
    apply (exwp_atomic_ext _ _ _ _ _ _ He).
    intros m e2 m2 efs Hs. destruct (ext_step_inv _ _ _ _ _ _ _ He Hs) as (ov & _ & ->).
    destruct ov; simpl; [left; rewrite to_of_val; eauto | by right].
  Qed.

  Lemma exwp_write_sc_atomic E1 E2 l v Φ :
    (|={E1,E2}=> EXWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E1 {{ Φ }}.
  Proof.
    assert (He : lr_external (Write ScOrd (Lit (LitLoc l)) (of_val v))
      (AStore tt l v) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). constructor. apply to_of_val. }
    apply (exwp_atomic_ext _ _ _ _ _ _ He).
    intros m e2 m2 efs Hs. destruct (ext_step_inv _ _ _ _ _ _ _ He Hs) as (ov & _ & ->).
    left. eauto.
  Qed.
End sc_rules.

(** Small proof-mode helpers using the sequential language's pure reductions. *)
From iris.proofmode Require Import coq_tactics reduction.
From lrust.lang Require Import tactics.

Lemma tac_exwp_bind `{!ExtCallSems lr_language, !lrSqGS Σ} K Δ E Φ e :
  envs_entails Δ (EXWP e @ E {{ v, EXWP fill K (of_val v) @ E {{ Φ }} }})%I ->
  envs_entails Δ (EXWP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. apply exwp_bind. Qed.

Lemma tac_exwp_pure `{!ExtCallSems lr_language, !lrSqGS Σ} K Δ Δ' E e1 e2 φ n Φ :
  @PureExec sq_lang φ n e1 e2 -> φ ->
  MaybeIntoLaterNEnvs n Δ Δ' ->
  envs_entails Δ' (EXWP fill K e2 @ E {{ Φ }}) ->
  envs_entails Δ (EXWP fill K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => Hexec Hφ ? HΔ.
  rewrite into_laterN_env_sound HΔ. apply exwp_pure_steps.
  exact (@pure_step_nsteps_ctx sq_lang (@ectx_language.fill sq_ectx_lang K)
    (@ectx_lang_ctx sq_ectx_lang K) n e1 e2 (Hexec Hφ)).
Qed.

Tactic Notation "exwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; apply (tac_exwp_bind K); simpl)
  end.

Tactic Notation "exwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; eapply (tac_exwp_pure K);
    [simpl; tc_solve | try done | tc_solve | simpl_subst])
  end.
