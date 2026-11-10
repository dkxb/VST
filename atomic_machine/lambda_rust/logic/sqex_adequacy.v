(** Adequacy of the lifted sequential logic over the atomic machine semantics
    of lambda-Rust. *)

From stdpp Require Import relations.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sq_adequacy.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Import ListNotations.

(** The external-call semantics.  *)
Class satisfy_conc_triples Σ `{!ExtCallSems lr_language} : Prop := {
  conc_wp_read_sc : forall `{!lrSqGS Σ} E l q v,
    {{{ ▷ l ↦{q} v }}} EXWP (Read ScOrd (Lit $ LitLoc l) : sq_expr) @ E
    {{{ RET (v : sq_val); l ↦{q} v }}};
  conc_wp_write_sc : forall `{!lrSqGS Σ} E l (e : sq_expr) v v',
    IntoVal e v ->
    {{{ ▷ l ↦ v' }}} EXWP (Write ScOrd (Lit $ LitLoc l) e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); l ↦ v }}};
  conc_wp_fork : forall `{!lrSqGS Σ} E (e : sq_expr),
    {{{ ▷ EXWP e {{ _, True }} }}} EXWP (Fork e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); True }}}
  (* other atomic operations *)
}.

(**  every allocated location is unreserved. *)
Definition sq_mu (m : lr_mem) : rw_map := (fun _ => Rst 0) <$> m.

Definition sqex_pool (tp : list sq_expr) : tpool :=
  map_seq 0%nat ((fun e => Running e []) <$> tp).

(** execution is safe and mem terminates in a state satisfying the postconditions. FIXME what should the initial rw_map be? *)
Definition at_sem_adequate (tp : list sq_expr) (φs : list (sq_val -> Prop)) (m : lr_mem) : Prop :=
  forall tp' m' mu',
    am_steps (AMCfg (sqex_pool tp) m (sq_mu m)) (AMCfg tp' m' mu') ->
    (forall i t, tp' !! i = Some t -> am_not_stuck t m' mu') /\
    (forall i e v φ, tp' !! i = Some (Running e []) -> to_val e = Some v ->
       φs !! i = Some φ -> φ v).

Section permission_resources.
  Context `{!lrSqGS Σ, !ExtCallSems lr_language}.

  (** A pending reservation keeps ownership outside the focused EXWP.
      One positive fraction suffices to witness pending readers; a pending
      writer keeps full ownership. This is a resource invariant, not an
      assertion that ownership can be extracted from an arbitrary EXWP. *)
  Local Definition sqex_reservation (l : loc) (st : rw_state) : iProp Σ :=
    match st with
    | Rst 0 => True
    | Rst (S _) => ∃ q v, l ↦{q} v
    | Wst => ∃ v, l ↦ v
    end.

  Local Definition sqex_reservations (mu : rw_map) : iProp Σ :=
    [∗ map] l ↦ st ∈ mu, sqex_reservation l st.

  (** Only this direction holds across a pending Free: Try removes physical
      memory before Commit removes the corresponding reader/writer entry. *)
  Local Definition sqex_live_entries (m : lr_mem) (mu : rw_map) : Prop :=
    forall l, is_Some (m !! l) -> is_Some (mu !! l).

  Local Lemma sqex_reservations_init m : ⊢ sqex_reservations (sq_mu m).
  Proof.
    rewrite /sqex_reservations /sq_mu big_sepM_fmap.
    iApply big_sepM_intro. by iIntros "!#" (l v Hl).
  Qed.

  (** A write excludes every nonzero reservation after one logical step.
      The physical footprint supplies allocation, and the framed ownership
      contradicts EXWP's mandatory version increment, including same-value
      writes. No ownership-extraction theorem is used. *)
  Local Lemma sqex_write_permitted E e Φ m ver_map mu T e' m' l :
    lr_step e m T e' m' -> lr_write_event l ∈ T ->
    sqex_live_entries m mu ->
    sq_heap_gen m ver_map -∗ EXWP e @ E {{ Φ }} -∗
    sqex_reservations mu -∗ ▷ ⌜mu !! l = Some (Rst 0)⌝.
  Proof.
    intros Hstep Hwrite Hlive.
    pose proof (lr_step_not_value _ _ _ _ _ Hstep) as Hv.
    pose proof (lr_step_not_external _ _ _ _ _ Hstep) as Hext.
    destruct (lr_step_write_footprint _ _ _ _ _ _ Hstep Hwrite)
      as (old & new & Hold & _).
    destruct (Hlive l (ex_intro _ old Hold)) as [st Hst].
    iIntros "Hσ Hwp Hresv".
    destruct st as [[|n]|].
    - iNext. done.
    - iDestruct (big_sepM_lookup _ _ l _ Hst with "Hresv") as (q v) "Hl".
      iPoseProof (sqex_write_frame _ _ _ _ _ _ _ _ _ _ _
        Hv Hext Hstep Hwrite with "Hσ Hwp Hl") as "Hbad".
      iNext. by iDestruct "Hbad" as %[].
    - iDestruct (big_sepM_lookup _ _ l _ Hst with "Hresv") as (v) "Hl".
      iPoseProof (sqex_write_frame _ _ _ _ _ _ _ _ _ _ _
        Hv Hext Hstep Hwrite with "Hσ Hwp Hl") as "Hbad".
      iNext. by iDestruct "Hbad" as %[].
  Qed.

  (** The focused thread remains thread 0 with no pending events at logical
      boundaries. Other threads contribute reservation resources, not progress
      or safety assertions. Establishing those resources through Try and spawn
      is a separate preservation obligation. *)
  Local Definition sqex_config_inv (φ : sq_val -> Prop) (e : sq_expr)
      (tp : tpool) (m : lr_mem) (mu : rw_map) : iProp Σ :=
    ∃ ver_map : loc -> nat, sq_heap_gen m ver_map ∗
      ⌜tp !! 0%nat = Some (Running e [])⌝ ∗ ⌜sqex_live_entries m mu⌝ ∗
      sqex_reservations mu ∗ EXWP e {{ v, ⌜φ v⌝ }}.

  Local Lemma sqex_config_inv_init φ e m :
    (⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
    sq_heap_gen m (fun _ => 0%nat) -∗
    sqex_config_inv φ e {[0%nat := Running e []]} m (sq_mu m).
  Proof.
    intros Hwp. iIntros "Hσ". iPoseProof Hwp as "Hwp".
    iExists (fun _ => 0%nat). iFrame "Hσ Hwp".
    iSplit; first done. iSplit.
    - iPureIntro. intros l [v Hv]. exists (Rst 0).
      by rewrite /sq_mu lookup_fmap Hv.
    - iApply sqex_reservations_init.
  Qed.
End permission_resources.

(** The sequential logic exposes progress without inspecting lr_step cases. *)
Local Lemma sqex_nonvalue_progress `{!lrSqGS Σ, !ExtCallSems lr_language}
    E (e : sq_expr) (Φ : sq_val -> iProp Σ) (m : lr_mem) (ver_map : loc -> nat) :
  to_val e = None ->
  EXWP e @ E {{ Φ }} -∗ sq_heap_gen m ver_map -∗
  ⌜(exists T e' m', lr_step e m T e' m') \/
    (exists op k, lr_external e op k)⌝.
Proof.
  intros Hv. iIntros "Hwp Hσ". iApply (bupd_elim _).
  iEval (rewrite exwp_unfold /exwp_pre Hv) in "Hwp".
  iMod "Hwp" as "[Hseq | [%Hcall _]]".
  - iMod ("Hseq" with "Hσ") as "[%Hred _]".
    iModIntro. iPureIntro. by left.
  - iModIntro. iPureIntro. by right.
Qed.

(** One sequential step gives a Try and, for a nonempty trace, a Commit.
    This proves existence of that execution, not safety of every interleaving. *)
Local Lemma sqex_lr_step_pair tp m mu i e T e' m' mu_try mu_done :
  tp !! i = Some (Running e []) -> lr_step e m T e' m' ->
  rsv T mu = Some mu_try -> atomic_machine.fin T mu_try = Some mu_done ->
  exists qmid, at_step (AMCfg tp m mu) qmid /\
    am_steps qmid (AMCfg (<[i := Running e' []]> tp) m' mu_done).
Proof.
  intros Hi Hstep Hrsv Hfin.
  exists (AMCfg (<[i := Running e' T]> tp) m' mu_try). split.
  - by eapply Core_Try.
  - destruct T as [|ev T].
    + simpl in Hfin. inversion Hfin; subst. apply rtc_refl.
    + unfold tpool in *. apply rtc_once.
      rewrite <- (insert_insert_eq tp i (Running e' []) (Running e' (ev :: T))).
      eapply Core_Commit with (T := ev :: T); [ | discriminate | exact Hfin ].
      apply (lookup_insert_eq (M := gmap nat)).
Qed.

(** A concrete interpretation for instantiating the external interface in
    [Hwp] and [Hsound]. It uses the memory operations of [lr_language]. *)
Local Definition sqex_adequacy_extcalls : ExtCallSems lr_language :=
  fun op m ov m' efs =>
    match op with
    | ALoad _ l =>
        exists v, m !! l = Some v /\ ov = Some v /\ m' = m /\ efs = []
    | AStore _ l v =>
        is_Some (m !! l) /\ ov = None /\ m' = <[l := v]> m /\ efs = []
    | ACAS _ l v_exp v_new =>
        exists v_cur, m !! l = Some v_cur /\ efs = [] /\
          ((lr_val_eq m v_cur v_exp /\
            ov = Some (LitV (lit_of_bool true)) /\ m' = <[l := v_new]> m) \/
           (lr_val_neq m v_cur v_exp /\
            ov = Some (LitV (lit_of_bool false)) /\ m' = m))
    | ASpawn e => ov = None /\ m' = m /\ efs = [e]
    end.

(** An exposed head call has a unique operation and continuation. *)
Local Lemma sqex_head_external_unique e op k op' k' :
  lr_head_external e op k -> lr_external e op' k' ->
  op' = op /\ forall ov, k' ov = k ov.
Proof.
  intros Hhead Hext.
  assert (Hshape : redex_shape e).
  { intros Ki e1 Heq. subst e. destruct Ki; inversion Hhead; subst;
      rewrite ?to_of_val; eauto. }
  inversion Hext as [K r op0 k0 Hr Heq]; subst.
  assert (Hvr : to_val r = None) by (destruct Hr; done).
  destruct (fill_redex_shape_inv K r (fill K r) Hshape Hvr eq_refl) as [-> _].
  simpl in Hhead |- *. destruct Hhead; inversion Hr; subst; split; congruence.
Qed.

Local Lemma sqex_ext_step_head `{!ExtCallSems lr_language}
    e op k m T e' m' efs :
  lr_head_external e op k -> ext_step (L := lr_language) e m T e' m' efs ->
  exists ov, extcall_sems op m ov m' efs /\ extcall_events op ov T /\ e' = k ov.
Proof.
  intros Hhead Hstep. destruct Hstep as [e op0 k0 m ov m' e' efs T He Hsem Htrace Ha].
  destruct (sqex_head_external_unique _ _ _ _ _ Hhead He) as [-> _].
  destruct Ha as [e op1 k1 ov He1].
  destruct (sqex_head_external_unique _ _ _ _ _ Hhead He1) as [_ Hk].
  exists ov. split; first exact Hsem. split; [exact Htrace | apply Hk].
Qed.

Section adequacy_external_model.
  Local Existing Instance sqex_adequacy_extcalls.

  Local Lemma sqex_adequacy_conc_triples Σ :
    @satisfy_conc_triples Σ sqex_adequacy_extcalls.
  Proof.
    constructor.
    - intros Hgs E l q v Φ. iIntros "Hl HΦ".
      iApply (exwp_lift_ext_step _ _ (ALoad tt l) lr_result_expr).
      { apply (LREctxExternal []). constructor. }
      iIntros (m ver_map) "Hm". iDestruct "Hl" as ">Hl".
      iDestruct (sq_heap_gen_read with "Hm Hl") as %Hm.
      iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
      iModIntro. iSplit.
      { iPureIntro. exists [], (of_val v), m, [].
        eapply ExtStep with (op := ALoad tt l) (ov := Some v).
        - apply (LREctxExternal []). constructor.
        - exists v. done.
        - constructor.
        - apply (LRAfterExternal _ (ALoad tt l) lr_result_expr).
          apply (LREctxExternal []). constructor. }
      iIntros (T e2 m2 efs Hstep).
      destruct (sqex_ext_step_head _ _ _ _ _ _ _ _ (LRReadScE l) Hstep)
        as (ov & Hsem & Htrace & ->).
      inversion Htrace; subst T.
      destruct Hsem as (w & Hw & -> & -> & ->).
      assert (w = v) as -> by congruence.
      iModIntro. iNext. iModIntro. iMod "Hclose" as "_".
      iModIntro. iFrame "Hm". rewrite big_sepL_nil right_id.
      rewrite exwp_value_bupd. iModIntro. by iApply "HΦ".
    - intros Hgs E l e v v' Hval Φ. iIntros "Hl HΦ".
      assert (Hv : to_val e = Some v).
      { rewrite -(@into_val sq_lang e v Hval). apply to_of_val. }
      iApply (exwp_lift_ext_step _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
      { apply (LREctxExternal []). by constructor. }
      iIntros (m ver_map) "Hm". iDestruct "Hl" as ">Hl".
      iDestruct (sq_heap_gen_read with "Hm Hl") as %Hm.
      iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
      iModIntro. iSplit.
      { iPureIntro. exists [lr_write_event l], (Lit LitPoison), (<[l := v]> m), [].
        eapply ExtStep with (op := AStore tt l v) (ov := None).
        - apply (LREctxExternal []). by constructor.
        - split; first by eexists. done.
        - constructor.
        - apply (LRAfterExternal _ (AStore tt l v) (fun _ => Lit LitPoison)).
          apply (LREctxExternal []). by constructor. }
      iIntros (T e2 m2 efs Hstep).
      destruct (sqex_ext_step_head _ _ _ _ _ _ _ _ (LRWriteScE l e v Hv) Hstep)
        as (ov & Hsem & Htrace & ->).
      inversion Htrace; subst T.
      destruct Hsem as (_ & -> & -> & ->).
      iModIntro. iNext. iModIntro. iMod "Hclose" as "_".
      iMod (sq_heap_gen_write_step _ _ _ _ v with "Hm Hl") as "[Hm Hl]".
      iModIntro. iFrame "Hm". rewrite big_sepL_nil right_id.
      rewrite exwp_unfold /exwp_pre /=. iModIntro. by iApply "HΦ".
    - intros Hgs E e Φ. iIntros "He HΦ".
      iApply (exwp_lift_ext_step _ _ (ASpawn e) (fun _ => Lit LitPoison)).
      { apply (LREctxExternal []). constructor. }
      iIntros (m ver_map) "Hm".
      iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
      iModIntro. iSplit.
      { iPureIntro. exists [], (Lit LitPoison), m, [e].
        eapply ExtStep with (op := ASpawn e) (ov := None).
        - apply (LREctxExternal []). constructor.
        - done.
        - constructor.
        - apply (LRAfterExternal _ (ASpawn e) (fun _ => Lit LitPoison)).
          apply (LREctxExternal []). constructor. }
      iIntros (T e2 m2 efs Hstep).
      destruct (sqex_ext_step_head _ _ _ _ _ _ _ _ (LRSpawnE e) Hstep)
        as (ov & Hsem & Htrace & ->).
      inversion Htrace; subst T.
      destruct Hsem as (-> & -> & ->).
      iModIntro. iNext. iModIntro. iMod "Hclose" as "_".
      iModIntro. iFrame "Hm". rewrite big_sepL_singleton. iFrame "He".
      rewrite exwp_unfold /exwp_pre /=. iModIntro. iApply "HΦ". done.
  Qed.
End adequacy_external_model.

(** The logical invariant follows only the main thread, with an empty
    pending list. Spawned threads must be handled in the spawn proof by
    recursive calls and a composition argument. *)
Theorem sqex_adequacy Σ
    `{!lrSqGpreS Σ}
    (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ} `{!ExtCallSems lr_language} `{!satisfy_conc_triples Σ},
  ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hwp.
  (* Starting from a singleton pool ensures every other thread arises at
     spawn. A main-thread invariant alone cannot establish safety of an
     arbitrary pre-existing pool. *)
  assert (Hsound : forall (Δ : gFunctors)
      `{!lrSqGS Δ},
    let Hsem : ExtCallSems lr_language := sqex_adequacy_extcalls in
    forall (φ0 : sq_val -> Prop) (e0 : sq_expr) (m0 : lr_mem) (mu0 : rw_map),
    sqex_config_inv φ0 e0 {[0%nat := Running e0 []]} m0 mu0 -∗
    ∀ n tp' m' mu' i t',
      ⌜nsteps at_step n (AMCfg {[0%nat := Running e0 []]} m0 mu0)
        (AMCfg tp' m' mu')⌝ -∗
      ⌜tp' !! i = Some t'⌝ -∗
      (* The extra logical step pays for checking endpoint permissions. *)
      |={⊤,∅}=> |={∅}▷=>^(S n)
        ⌜am_not_stuck t' m' mu' /\
          (i = 0%nat -> forall e0 v, t' = Running e0 [] ->
            to_val e0 = Some v -> φ0 v)⌝).
  2: {
    intros tp' m' mu' Hrtc.
    change (rtc at_step (AMCfg {[0%nat := Running e []]} m (sq_mu m))
      (AMCfg tp' m' mu')) in Hrtc.
    destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hsteps].
    assert (Hendpoint : forall i t, tp' !! i = Some t ->
      am_not_stuck t m' mu' /\
        (i = 0%nat -> forall e0 v, t = Running e0 [] ->
          to_val e0 = Some v -> φ v)).
    { intros i t Hi.
      apply (pure_soundness (PROP := iPropI Σ)).
      apply (step_fupdN_soundness_lc (Σ := Σ) _ (S n) 0).
      intros Hinv. iIntros "_".
      iMod (ghost_map_alloc (sq_heap_cells m (fun _ => 0%nat))) as (vγ) "[Hm _]".
      iMod (own_alloc (● (∅ : sq_freeableUR))) as (fγ) "Hf";
        first by apply auth_auth_valid.
      set (Hheap := SqHeapGS _ _ _ vγ fγ).
      set (Hgs := LrSqGS _ Hinv Hheap).
      pose proof (@Hwp Hgs sqex_adequacy_extcalls
        (sqex_adequacy_conc_triples Σ)) as Hclosed.
      iPoseProof (@Hsound Σ Hgs φ e m (sq_mu m)
        with "[Hm Hf]") as "Hrun".
      { iApply (sqex_config_inv_init _ _ _ Hclosed with "[Hm Hf]").
        iExists ∅. iFrame. iPureIntro.
        intros b qs Hlookup. by rewrite lookup_empty in Hlookup. }
      by iApply ("Hrun" $! n tp' m' mu' i t with "[] []"). }
    split.
    - intros i t Hi. exact (proj1 (Hendpoint i t Hi)).
    - intros i e0 v φ0 Hi Hv Hφ.
      destruct i as [|i]; simpl in Hφ; last by discriminate.
      inversion Hφ; subst φ0.
      exact (proj2 (Hendpoint 0%nat (Running e0 []) Hi) eq_refl e0 v eq_refl Hv).
  }
  intros Δ Hgs Hsem φ0 e0 m0 mu0.
  iLöb as "IH" forall (φ0 e0 m0 mu0).
  iIntros "(%ver_map & Hσ & %Hmain & %Hlive & Hresv & Hwp)"
    (n tp' m' mu' i t Hsteps Hi).
  destruct n as [|n].
  - inversion Hsteps; subst tp' m' mu'. simpl.
    apply (lookup_singleton_Some (M := gmap nat)) in Hi as [Hindex Hthread].
    subst i t.
    destruct (to_val e0) as [v|] eqn:Hv.
    + iEval (rewrite exwp_unfold /exwp_pre Hv) in "Hwp".
      iMod "Hwp" as "%Hpost".
      iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
      iModIntro. iModIntro. iNext. iModIntro. iPureIntro. split.
      { left. exists e0. split; first done. by exists v. }
      intros _ e1 w Heq Hw. inversion Heq; subst e1.
      rewrite Hv in Hw. inversion Hw; subst w. exact Hpost.
    + iAssert ((⌜(exists T e1 m1, lr_step e0 m0 T e1 m1) \/
          (exists op k, lr_external e0 op k)⌝) ∧
          (sq_heap_gen m0 ver_map ∗ EXWP e0 {{ v, ⌜φ0 v⌝ }}))%I
          with "[Hσ Hwp]" as "[%Hprogress [Hσ Hwp]]".
      { iSplit; last by iFrame.
        by iApply (sqex_nonvalue_progress ⊤ e0
          (fun v => ⌜φ0 v⌝)%I m0 ver_map Hv with "Hwp Hσ"). }
      destruct Hprogress as [Hred | Hcall].
      * destruct Hred as (T & e1 & m1 & Hstep).
        iAssert (▷ ⌜lr_events_permitted mu0 T⌝)%I
          with "[Hσ Hwp Hresv]" as "Hpermitted".
        2: {
          iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
          iModIntro. iModIntro. iNext. iModIntro.
          iDestruct "Hpermitted" as %Hpermitted.
          destruct (lr_step_rsv_fin _ _ _ _ _ _ Hstep Hpermitted)
            as (mu_try & mu_done & Hreserve & Hcommit).
          destruct (sqex_lr_step_pair {[0%nat := Running e0 []]} _ _ 0%nat
            _ _ _ _ _ _ (lookup_singleton_eq (M := gmap nat) 0%nat (Running e0 []))
            Hstep Hreserve Hcommit) as (qmid & Hfirst & Htail).
          iPureIntro. split.
          - right. by exists qmid.
          - intros _ e3 w Heq Hw. inversion Heq; subst e3. congruence.
        }
        iIntros (l). iSplit.
        -- iIntros (Hwrite).
           iApply (sqex_write_permitted _ _ _ _ _ _ _ _ _ _
             Hstep Hwrite Hlive
             with "Hσ Hwp Hresv").
        -- iSplit.
           ++ iIntros (Hread).
              destruct (lr_step_read_footprint _ _ _ _ _ _ Hstep Hread)
                as (Hallocated & _).
              destruct (Hlive l Hallocated) as [st Hst].
              destruct st as [n|].
              { iNext. iPureIntro. by exists n. }
              iDestruct (big_sepM_lookup _ _ l _ Hst with "Hresv") as (v) "Hwriter".
              iAssert (▷ False)%I with "[Hσ Hwp Hwriter]" as "Hbad".
              2: { iNext. by iDestruct "Hbad" as %[]. }
              (* The write clause above is now proved from framed reservation
                 resources under one later. The remaining read clause needs
                 to exclude a pending writer. Reads do not change versions,
                 so the write-frame argument does not establish it.

                 In the current heap model, freeability can prove allocation
                 without points-to ownership: [†l…1] suffices for the EXWP of
                 a read with postcondition [True]. That EXWP can coexist with
                 full points-to held in a pending writer's frame. Thus even
                 a guarded read-versus-writer exclusion needs a stronger
                 connection between logical read access and reservations.

                 Preservation must also construct the reservation resources
                 at Try, retain them until Commit, and compose spawned
                 threads using the induction hypothesis. Allocation requires
                 choosing a location fresh in both memory and mu; pending
                 Free means their domains need not coincide. *)
Admitted.
