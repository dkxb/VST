(** Compositional rules for EXWP. External calls and spawning admit fancy updates. *)
From iris.algebra Require Import auth gmap.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.at_logic.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

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

Lemma lr_external_fill_inv K e op k :
  to_val e = None -> lr_external (fill K e) op k ->
  exists k', lr_external e op k' /\ forall ov, k ov = fill K (k' ov).
Proof.
  intros Hv He. inversion He as [K' r op' kr Hh Heq]; subst.
  destruct (fill_decompose K K' e r (lr_head_external_redex_shape _ _ _ Hh)
    (lr_head_external_not_val _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
  exists (fun ov => fill K'' (kr ov)). split; first by constructor.
  intro ov. by rewrite fill_app.
Qed.

Section rules.
  Context `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ}.

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
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit.
      { iPureIntro. intros op k He.
        destruct (lr_external_fill_inv _ _ _ _ Hv He) as (k' & He' & _).
        by eapply Hno. }
      iIntros (m h) "Hm". iMod ("Hseq" with "Hm") as "[%Hr Hstep]".
      iModIntro. iSplit.
      { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
        exists T, (fill K e2), m2. destruct Hs. rewrite -!fill_app. by constructor. }
      iIntros (T e2 m2 Hs).
      inversion Hs as [K' r m0 T0 r' m0' Hh Heq]; subst.
      destruct (fill_decompose K K' e r (lr_head_step_redex_shape _ _ _ _ _ Hh)
        (lr_head_step_not_val _ _ _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
      iDestruct ("Hstep" $! T (fill K'' r') m2 with "[%]") as "Hstep".
      { by constructor. }
      iNext. iMod "Hstep" as (h2) "(Hperm & Hm & Hwp)".
      iModIntro. iExists h2. iFrame. rewrite fill_app. by iApply "IH".
    - destruct (lr_external_fill K _ _ _ He) as (k' & He' & Hk).
      iRight. iExists op, k'. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
      iModIntro. rewrite Hk. by iApply "IH".
  Qed.

  (** The logical parameters may be chosen after opening invariants. *)
  Lemma exwp_ext_unfold E e op k Φ :
    lr_external e op k ->
    EXWP e @ E {{ Φ }} ⊣⊢
      (|={E,∅}=> ∃ x : ext_spec_args op,
        ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) ∗
        ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> EXWP k ov @ E {{ Φ }})).
  Proof.
    intros He. iSplit; last by iApply (exwp_lift_external _ _ _ _ _ He).
    rewrite exwp_unfold /exwp_pre (lr_external_not_val _ _ _ He).
    iIntros ">[[%Hno _] | (%op' & %k' & %He' & Hspec)]".
    - exfalso. by eapply Hno.
    - destruct (lr_external_det _ _ _ _ _ He He') as [-> Hk].
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". rewrite -(Hk ov). by iApply "Hcont".
  Qed.

  Lemma exwp_stuck E Φ m h :
    sq_heap_gen m h -∗ EXWP stuck_term @ E {{ Φ }} ==∗ False.
  Proof.
    assert (Hr : redex_shape stuck_term).
    { unfold stuck_term. intros Ki e He; destruct Ki; simpl in He;
        simplify_eq; eauto; discriminate_list. }
    rewrite exwp_seq_unfold; [ | done | ].
    - iIntros "Hm Hwp". iMod ("Hwp" with "Hm") as "[%Hs _]".
      destruct Hs as (T & e2 & m2 & Hs). apply lr_step_head in Hs; [inversion Hs | done].
    - intros op k He. apply lr_external_head in He; [inversion He | done].
  Qed.

  (** A call is atomic for mask changes when its specification guarantees
      that the continuation returns a value. *)
  Lemma exwp_atomic_ext E1 E2 e op k Φ :
    lr_external e op k ->
    (forall x ov, ext_spec_post op x ov ⊢ ⌜is_Some (to_val (k ov))⌝) ->
    (|={E1,E2}=> EXWP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
      EXWP e @ E1 {{ Φ }}.
  Proof.
    intros He Ha. iIntros "Hwp".
    iApply (exwp_lift_external _ _ _ _ _ He).
    iMod "Hwp" as "Hwp".
    iEval (rewrite (exwp_ext_unfold _ _ _ _ _ He)) in "Hwp".
    iMod "Hwp" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
    iNext. iIntros (ov) "Hpost".
    iDestruct (Ha with "Hpost") as %[v Hv].
    iMod ("Hcont" with "Hpost") as "Hwp".
    apply of_to_val in Hv as <-. rewrite !exwp_value_bupd.
    iMod "Hwp" as ">HΦ". by iModIntro.
  Qed.

  Lemma exwp_pure_step E e1 e2 Φ :
    @pure_step sq_lang e1 e2 ->
    ▷ EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    intros [Hsafe Hdet].
    assert (Hv : to_val e1 = None).
    { destruct (Hsafe ∅) as (e' & m' & efs & Hs). exact (language.val_stuck _ _ _ _ _ _ Hs). }
    iIntros "Hwp". iApply exwp_lift_step; first done.
    { destruct (Hsafe ∅) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      by eapply lr_step_not_external. }
    iIntros (m h) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (Hsafe m) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      eauto. }
    iIntros (T e' m' Hs).
    destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
    { by apply sq_prim_step_lr_step. }
    iNext. iModIntro. iExists h. iFrame. iPureIntro. constructor.
  Qed.

  Lemma exwp_pure_steps E e1 e2 Φ n :
    nsteps (@pure_step sq_lang) n e1 e2 ->
    ▷^n EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    induction 1 as [e | n e1 e2 e3 Hs Hsteps IH]; first done.
    simpl. iIntros "H". iApply (exwp_pure_step _ _ _ _ Hs).
    iNext. by iApply IH.
  Qed.

  Lemma exwp_read_na E l q v :
    l ↦{q} v -∗ EXWP (Read Na1Ord (Lit (LitLoc l))) @ E
      {{ w, ⌜w = v⌝ ∗ l ↦{q} v }}.
  Proof.
    iIntros "Hl". iApply exwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m h) "Hm".
    iDestruct (sq_heap_gen_read with "Hm Hl") as %Hl.
    iDestruct (sq_heap_gen_lookup with "Hm Hl") as %(_ & qt & Hperm & _).
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRReadNaS. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. simplify_map_eq. iNext.
    iModIntro. iExists h. iSplit.
    { iPureIntro. econstructor; [by eapply PermRead | constructor]. }
    iFrame "Hm". iApply exwp_value. by iFrame.
  Qed.

  (** Non-atomic writes require full thread ownership. *)
  Lemma exwp_write_na E l v v' :
    l ↦ v -∗ EXWP (Write Na1Ord (Lit (LitLoc l)) (of_val v')) @ E
      {{ _, l ↦ v' }}.
  Proof.
    iIntros "Hl". iApply exwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m h) "Hm".
    iDestruct (sq_heap_gen_read with "Hm Hl") as %Hl.
    iDestruct (sq_heap_gen_full with "Hm Hl") as %Hperm.
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []).
      econstructor; [apply to_of_val | exact Hl]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst.
    match goal with H : to_val (of_val _) = Some _ |- _ =>
      rewrite to_of_val in H; injection H as <- end.
    iNext. iMod (sq_heap_gen_write with "Hm Hl") as "[Hm Hl]".
    iModIntro. iExists h. iSplit.
    { iPureIntro. econstructor; [by eapply PermWrite | constructor]. }
    iFrame "Hm". by iApply (exwp_value _ (LitV LitPoison)).
  Qed.

  Lemma exwp_alloc E Φ :
    (▷ ∀ l, l ↦ LitV LitPoison -∗ Φ (LitV (LitLoc l))) -∗
    EXWP (Alloc (Lit (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply exwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m h) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
      do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext.
    iDestruct (sq_heap_gen_missing m h l with "Hm") as %Hnone.
    { by rewrite -(shift_loc_0 l). }
    iMod (sq_heap_gen_alloc _ _ _ 1 with "Hm") as "[Hm [_ Hl]]"; [lia | done | ].
    rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
    iModIntro. iExists (<[l := 1%Qp]> h). iSplit.
    { iPureIntro. econstructor; [by apply PermAlloc | constructor]. }
    iFrame. iApply (exwp_value _ (LitV (LitLoc l))). by iApply "HΦ".
  Qed.
End rules.

(** The contracts used by the SC examples. CAS has no contract in this
    collection; clients can supply a different [ExtCallSpecs] collection. *)
Definition lr_ext_args (op : @atomic_op loc val lr_layout expr) : Type :=
  match op with
  | ALoad _ _ => Qp * val
  | AStore _ _ _ => val
  | ACAS _ _ _ _ => Empty_set
  | ASpawn _ => unit
  end.

Section concurrent_specs.
  Context `{!lrSqGS Σ}.

  Definition lr_ext_pre (op : @atomic_op loc val lr_layout expr) :
      lr_ext_args op -> (sq_expr -> iProp Σ) -> iProp Σ :=
    match op as op return lr_ext_args op -> (sq_expr -> iProp Σ) -> iProp Σ with
    | ALoad _ l => fun qv _ => l ↦{qv.1} qv.2
    | AStore _ l _ => fun v _ => l ↦ v
    | ACAS _ _ _ _ => fun x _ => match x with end
    | ASpawn e => fun _ W => W e
    end%I.

  Local Instance lr_ext_pre_ne op x :
    NonExpansive (lr_ext_pre op x : (sq_expr -d> iPropO Σ) -> iPropO Σ).
  Proof. intros n W W' HW. destruct op; simpl; done. Qed.

  Definition lr_ext_post (op : @atomic_op loc val lr_layout expr) :
      lr_ext_args op -> option val -> iProp Σ :=
    match op as op return lr_ext_args op -> option val -> iProp Σ with
    | ALoad _ l => fun qv ov => ⌜ov = Some qv.2⌝ ∗ l ↦{qv.1} qv.2
    | AStore _ l v => fun _ ov => ⌜ov = None⌝ ∗ l ↦ v
    | ACAS _ _ _ _ => fun x _ => match x with end
    | ASpawn _ => fun _ ov => ⌜ov = None⌝
    end%I.

  Definition lr_ext_specs : ExtCallSpecs lr_language Σ :=
    {| ext_spec_args := lr_ext_args;
       ext_spec_pre op x := OfeMor (lr_ext_pre op x :
         (sq_expr -d> iPropO Σ) -> iPropO Σ);
       ext_spec_post := lr_ext_post |}.
End concurrent_specs.

Section concurrent_rules.
  Context `{!lrSqGS Σ}.
  Local Existing Instance lr_ext_specs.

  Lemma conc_wp_read_sc E l q v :
    {{{ ▷ l ↦{q} v }}} EXWP (Read ScOrd (Lit $ LitLoc l) : sq_expr) @ E
    {{{ RET (v : sq_val); l ↦{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iApply (exwp_lift_external _ _ (ALoad tt l) lr_result_expr).
    { apply (LREctxExternal []). constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists (q, v). simpl. iFrame "Hl".
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply exwp_value. by iApply "HΦ".
  Qed.

  Lemma conc_wp_write_sc E l (e : sq_expr) v v' :
    IntoVal e v ->
    {{{ ▷ l ↦ v' }}} EXWP (Write ScOrd (Lit $ LitLoc l) e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); l ↦ v }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    assert (Hv : to_val e = Some v).
    { rewrite -(@into_val sq_lang e v Hval). apply to_of_val. }
    iApply (exwp_lift_external _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). by constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists v'. simpl. iFrame "Hl".
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply (exwp_value _ (LitV LitPoison)). by iApply "HΦ".
  Qed.

  Lemma conc_wp_fork E (e : sq_expr) :
    {{{ ▷ EXWP e {{ _, True }} }}} EXWP (Fork e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); True }}}.
  Proof.
    iIntros (Φ) "He HΦ".
    iApply (exwp_lift_external _ _ (ASpawn e) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iModIntro. iExists (). simpl. iFrame "He".
    iNext. iIntros (ov) "->". iMod "Hclose" as "_".
    iModIntro. iApply (exwp_value _ (LitV LitPoison)). iApply "HΦ". done.
  Qed.

  Lemma exwp_read_sc_atomic E1 E2 l Φ :
    (|={E1,E2}=> EXWP (Read ScOrd (Lit (LitLoc l))) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (Read ScOrd (Lit (LitLoc l))) @ E1 {{ Φ }}.
  Proof.
    eapply (exwp_atomic_ext _ _ _ (ALoad tt l) lr_result_expr).
    - apply (LREctxExternal []). constructor.
    - intros [q v] ov. simpl. iIntros "[-> _]".
      iPureIntro. exists v. apply to_of_val.
  Qed.

  Lemma exwp_write_sc_atomic E1 E2 l v Φ :
    (|={E1,E2}=> EXWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E1 {{ Φ }}.
  Proof.
    eapply (exwp_atomic_ext _ _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
    - apply (LREctxExternal []). constructor. apply to_of_val.
    - intros x ov. iIntros "_". eauto.
  Qed.
End concurrent_rules.

(** Small proof-mode helpers using the sequential language's pure reductions. *)
From iris.proofmode Require Import coq_tactics reduction.
From lrust.lang Require Import tactics.

Lemma tac_exwp_bind `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} K Δ E Φ e :
  envs_entails Δ (EXWP e @ E {{ v, EXWP fill K (of_val v) @ E {{ Φ }} }})%I ->
  envs_entails Δ (EXWP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. apply exwp_bind. Qed.

Lemma tac_exwp_pure `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} K Δ Δ' E e1 e2 φ n Φ :
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
