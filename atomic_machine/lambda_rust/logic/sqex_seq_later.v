(** Retaining a sequential heap budget across nested basic updates and later. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_resources.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_resource_split.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_auth_full.
From iris.algebra Require Import auth functions gmap.
From iris.base_logic Require Import bi derived.

Set Default Proof Using "Type".

Section camera_frames.
  Context {A : ucmra}.

  Lemma sqex_auth_frame_boundN n (a b f : A) x `{!Cancelable b} :
    a ≡{n}≡ b ⋅ f ->
    ✓{n} (Some (● a ⋅ ◯ b) ⋅ x) -> x ≼{n} Some (◯ f).
  Proof.
    intros Hshape Hvalid.
    eapply (sqex_auth_option_cancel_frameN n a f b x).
    - by rewrite comm.
    - rewrite -assoc (comm op x) assoc -Some_op. exact Hvalid.
  Qed.

  Lemma sqex_auth_fill_frameN n (a c f : A) :
    ✓{n} (Some (● a ⋅ ◯ c) ⋅ Some (◯ f)) ->
    exists b, a ≡{n}≡ b ⋅ f ∧ c ≼{n} b ∧
      ✓{n} (Some (● a ⋅ ◯ b) ⋅ Some (◯ f)).
  Proof.
    rewrite -Some_op Some_validN -assoc -auth_frag_op auth_both_validN.
    intros [[d Hd] Ha].
    have Hshape : a ≡{n}≡ (c ⋅ d) ⋅ f by rewrite Hd -assoc (comm op f d) assoc.
    exists (c ⋅ d). split; first done. split; first apply cmra_includedN_l.
    rewrite -Some_op Some_validN -assoc -auth_frag_op auth_both_validN.
    split; last done. by rewrite Hshape.
  Qed.
End camera_frames.

Section projection_entailment.
  Context {Σ : gFunctors} {A : cmra} `{i : !inG Σ A}.

  Lemma sqex_own_project_equiv γ (r : iResUR Σ) (a : A) :
    sqex_project γ r ≡ Some a -> uPred_ownM r ⊢ own γ a.
  Proof.
    intros Hproject. destruct (sqex_project γ r) as [a'|] eqn:Hp.
    - have Heq : a' ≡ a by apply (inj Some).
      rewrite -Heq. by apply sqex_own_project.
    - inversion Hproject.
  Qed.
End projection_entailment.

Section delayed_update_frame.
  Context {Σ : gFunctors} {A : ucmra} `{i : !inG Σ (authR A)}.
  Context `{!CmraDiscrete A}.
  Context (Hcancel : forall x : A, Cancelable x).
  Local Existing Instance Hcancel.
  Local Notation erase := (@sqex_erase Σ (authR A) i).
  Local Notation project := (@sqex_project Σ (authR A) i).

  Definition sqex_state_update_post {I : Type}
      (a b : A) (S' : I -> iResUR Σ) (a' b' : I -> A) (Q : I -> iProp Σ) : iProp Σ :=
    ∃ z, ⌜(a, b) ~l~> (a' z, b' z)⌝ ∗ uPred_ownM (S' z) ∗ Q z.

  Lemma sqex_bupd_later_state_retain_core {I : Type}
      γ (a b f : A) (S r : iResUR Σ) (S' : I -> iResUR Σ) (a' b' : I -> A)
      (P : iProp Σ) (Q : I -> iProp Σ) :
    project γ S ≡ Some (● a) ->
    sqex_fragment_only b (project γ r) -> a ≡ b ⋅ f ->
    (forall z, project γ (S' z) ≡ Some (● (a' z))) ->
    (forall n x, (0 < n)%nat -> ✓{n} x ->
      uPred_holds (▷ |==> sqex_state_update_post a b S' a' b' Q) n x ->
      exists am c, project γ x ≡ Some (● am ⋅ ◯ c)) ->
    (uPred_ownM S ∗ P ⊢ |==> ▷ |==> sqex_state_update_post a b S' a' b' Q) ->
    uPred_ownM S ∗ uPred_ownM r ∗ sqex_support P r ⊢ |==> ▷ |==>
      ∃ z r', uPred_ownM (S' z) ∗ uPred_ownM r' ∗ sqex_support (Q z) r' ∗
        ⌜project γ r' ≡ Some (◯ (b' z))⌝.
  Proof using Type*.
    intros HS Hfragment Hshape HS' Hforce [Hupdate]. revert Hforce Hupdate.
    rewrite /sqex_state_update_post. uPred.unseal. try siProp_primitive.unseal.
    intros Hforce Hupdate. split.
    intros n x Hvalid (xs & xt & Hx & HSown & xr & xp & Ht & Hrown & Hsupport).
    have Hrx : S ⋅ r ≼{n} x.
    { rewrite Hx Ht. apply cmra_monoN; first exact HSown.
      etrans; first exact Hrown. apply cmra_includedN_l. }
    have Hsrvalid : ✓{n} (S ⋅ r) by eapply cmra_validN_includedN.
    have Hrvalid : ✓{n} r by eapply cmra_validN_op_r.
    have HP := sqex_support_holds P n r xp Hrvalid Hsupport.
    have Hpre : exists y1 y2, (S ⋅ r) ≡{n}≡ y1 ⋅ y2 ∧
        S ≼{n} y1 ∧ uPred_holds P n y2.
    { exists S, r. split; first done. split; [change (S ≼{n} S); done | exact HP]. }
    specialize (Hupdate n (S ⋅ r) Hsrvalid Hpre).
    intros k yf Hkn Hxy.
    have Hsry : ✓{k} ((S ⋅ r) ⋅ yf).
    { eapply cmra_validN_includedN; first exact Hxy.
      apply cmra_monoN_r. by eapply cmra_includedN_le. }
    destruct k as [|k]; first by exists (S ⋅ r).
    have Herase : ✓{Datatypes.S k} (erase γ (S ⋅ r) ⋅ erase γ yf).
    { rewrite -sqex_erase_op. by apply sqex_erase_validN. }
    have Hproject : ✓{Datatypes.S k} ((Some (● a) ⋅ project γ r) ⋅ project γ yf).
    { have Hp := @sqex_project_validN Σ (authR A) i (Datatypes.S k) γ _ Hsry.
      by rewrite !sqex_project_op HS in Hp. }
    have Ha : ✓{Datatypes.S k} a.
    { have Hauth : ✓{Datatypes.S k} (Some (● a) ⋅ project γ r) by eapply cmra_validN_op_l.
      exact (proj2 (sqex_auth_option_frame _ _ _ Hauth)). }
    have Hnormal : ✓{Datatypes.S k} (Some (● a ⋅ ◯ b) ⋅ project γ yf).
    { rewrite Some_op (comm op (Some (● a)) (Some (◯ b))) -assoc.
      apply (proj1 (sqex_fragment_only_validN (Datatypes.S k) b (project γ r)
        (Some (● a) ⋅ project γ yf) Hfragment)).
      by rewrite assoc (comm op (project γ r) (Some (● a))). }
    have Hybound : project γ yf ≼{Datatypes.S k} Some (◯ f).
    { eapply (sqex_auth_frame_boundN (Datatypes.S k) a b f (project γ yf));
        [by rewrite Hshape | exact Hnormal]. }
    have Hsat : ✓{Datatypes.S k} ((S ⋅ r) ⋅ sqex_replace γ (Some (◯ f)) yf).
    { rewrite comm sqex_replace_op_validN. split.
      - rewrite sqex_project_op HS.
        rewrite (comm op (Some (◯ f)) (Some (● a) ⋅ project γ r))
          (comm op (Some (● a)) (project γ r)) -assoc.
        rewrite (sqex_fragment_only_validN (Datatypes.S k) b (project γ r)
          (Some (● a) ⋅ Some (◯ f)) Hfragment).
        rewrite assoc (comm op (Some (◯ b)) (Some (● a))) -assoc.
        rewrite -!Some_op -auth_frag_op Some_validN auth_both_validN.
        split; [by rewrite Hshape | exact Ha].
      - by rewrite comm. }
    destruct (Hupdate (Datatypes.S k) (sqex_replace γ (Some (◯ f)) yf) Hkn Hsat)
      as (out & Houtvalid & Hlater).
    have Houtv : ✓{Datatypes.S k} out by eapply cmra_validN_op_l.
    destruct (Hforce (Datatypes.S k) out ltac:(lia) Houtv Hlater) as (am & c & Hfull).
    have Hparts : ✓{Datatypes.S k} (Some (● am ⋅ ◯ c) ⋅ Some (◯ f)) ∧
        ✓{Datatypes.S k} (erase γ out ⋅ erase γ yf).
    { rewrite comm sqex_replace_op_validN in Houtvalid.
      split.
      - rewrite comm -Hfull. exact (proj1 Houtvalid).
      - rewrite comm. exact (proj2 Houtvalid). }
    destruct (sqex_auth_fill_frameN _ _ _ _ (proj1 Hparts)) as (bm & Hmshape & Hcm & Hmvalid).
    have Hmshape' : am ≡ bm ⋅ f.
    { apply (proj2 (discrete_iff (Datatypes.S k) am (bm ⋅ f))). exact Hmshape. }
    set (mid := sqex_replace γ (Some (● am ⋅ ◯ bm)) out).
    have Hmono : out ≼{Datatypes.S k} mid.
    { apply sqex_replace_monoN. rewrite Hfull.
      apply Some_includedN. right. apply cmra_monoN_l.
      destruct Hcm as [d Hd]. exists (◯ d). by rewrite -auth_frag_op Hd. }
    have Hmidproject : project γ mid ≡ Some (● am ⋅ ◯ bm) by apply sqex_project_replace.
    have Hmidvalid : ✓{Datatypes.S k} (mid ⋅ yf).
    { rewrite /mid sqex_replace_op_validN. split; last exact (proj2 Hparts).
      eapply cmra_validN_includedN; first exact Hmvalid.
      by apply cmra_monoN_l. }
    have Hinner : uPred_holds (|==> sqex_state_update_post a b S' a' b' Q) k mid.
    { eapply uPred_mono.
      - rewrite /sqex_state_update_post !iris.base_logic.bi.uPred.uPred_unseal /=. exact Hlater.
      - eapply cmra_includedN_le; [exact Hmono | exact (Nat.le_succ_diag_r k)].
      - done. }
    exists mid. split; first exact Hmidvalid.
    rewrite /sqex_state_update_post !iris.base_logic.bi.uPred.uPred_unseal /= in Hinner.
    intros j zf Hjk Hmidzf.
    have Hzbound : project γ zf ≼{j} Some (◯ f).
    { eapply (sqex_auth_frame_boundN j am bm f (project γ zf)); first by rewrite Hmshape'.
      have Hp := @sqex_project_validN Σ (authR A) i j γ _ Hmidzf.
      by rewrite sqex_project_op Hmidproject in Hp. }
    have Hmid : ✓{j} mid by eapply cmra_validN_op_l.
    have Hsat2 : ✓{j} (mid ⋅ sqex_replace γ (Some (◯ f)) zf).
    { rewrite comm sqex_replace_op_validN. split.
      - rewrite Hmidproject comm. eapply cmra_validN_le; first exact Hmvalid.
        exact (Nat.le_trans j k (Datatypes.S k) Hjk (Nat.le_succ_diag_r k)).
      - rewrite comm -sqex_erase_op. by apply sqex_erase_validN. }
    destruct (Hinner j (sqex_replace γ (Some (◯ f)) zf) Hjk Hsat2)
      as (out' & Houtvalid' & z & xlu & xrest & Hout & Hlocal & xstate & xq & Hrest & Hstate & HQ).
    destruct Hstate as [res Hstate].
    set (rq := res ⋅ xq ⋅ xlu).
    have Hout_eq : out' ≡{j}≡ S' z ⋅ rq.
    { rewrite Hout Hrest Hstate /rq (comm op xlu) -!assoc. done. }
    have HQr : uPred_holds (Q z) j rq.
    { eapply uPred_mono; [exact HQ | | done].
      rewrite /rq. etrans; [apply cmra_includedN_r | apply cmra_includedN_l]. }
    have Hparts' : ✓{j} (Some (◯ f) ⋅ (Some (● (a' z)) ⋅ project γ rq)) ∧
        ✓{j} (erase γ zf ⋅ erase γ (S' z ⋅ rq)).
    { rewrite Hout_eq comm sqex_replace_op_validN sqex_project_op HS' in Houtvalid'. done. }
    have Ha_j : ✓{j} a.
    { eapply cmra_validN_le; first exact Ha.
      exact (Nat.le_trans j k (Datatypes.S k) Hjk (Nat.le_succ_diag_r k)). }
    have Htrans : ✓{j} (a' z) ∧ a' z ≡{j}≡ b' z ⋅ f.
    { apply (proj1 (local_update_unital _ _ _ _) Hlocal j f Ha_j).
      by rewrite Hshape. }
    set (rnew := sqex_replace γ (Some (◯ (b' z))) rq).
    have Hmono' : rq ≼{j} rnew.
    { apply sqex_replace_monoN.
      eapply (sqex_auth_option_cancel_frameN j (a' z) (b' z) f (project γ rq)).
      - exact (proj2 Htrans).
      - rewrite comm. exact (proj1 Hparts'). }
    have Hnewvalid : ✓{j} ((S' z ⋅ rnew) ⋅ zf).
    { rewrite (comm op (S' z) rnew) -assoc /rnew sqex_replace_op_validN.
      split.
      - rewrite sqex_project_op HS' assoc (comm op (Some (◯ (b' z))) (Some (● (a' z)))).
        have Htarget : ✓{j} ((Some (● (a' z)) ⋅ Some (◯ (b' z))) ⋅ Some (◯ f)).
        { rewrite -!Some_op Some_validN -assoc -auth_frag_op auth_both_validN.
          split; [by rewrite (proj2 Htrans) | exact (proj1 Htrans)]. }
        eapply cmra_validN_includedN; first exact Htarget.
        by apply cmra_monoN_l.
      - rewrite sqex_erase_op.
        have Hnonheap := proj2 Hparts'. rewrite sqex_erase_op in Hnonheap.
        rewrite (comm op (erase γ rq) (erase γ (S' z) ⋅ erase γ zf)).
        rewrite assoc (comm op (erase γ zf) (erase γ (S' z))) in Hnonheap.
        exact Hnonheap. }
    have HQnew : uPred_holds (Q z) j rnew by eapply uPred_mono; eauto.
    exists (S' z ⋅ rnew). split; first exact Hnewvalid.
    exists z. exists rnew. exists (S' z), rnew. split; first done.
    split; first (change (S' z ≼{j} S' z); done).
    exists rnew, ε. split; first by rewrite right_id.
    split; first (change (rnew ≼{j} rnew); done).
    exists ε, ε. split; first by rewrite left_id. split.
    - by apply sqex_support_of_holds.
    - apply sqex_project_replace.
  Qed.

  Lemma sqex_bupd_later_state_retain_fragment {I : Type}
      γ (a b f : A) (S r : iResUR Σ) (S' : I -> iResUR Σ) (a' b' : I -> A)
      (P : iProp Σ) (Q : I -> iProp Σ) :
    project γ S ≡ Some (● a) ->
    sqex_fragment_only b (project γ r) -> a ≡ b ⋅ f ->
    (forall z, project γ (S' z) ≡ Some (● (a' z))) ->
    (uPred_ownM S ∗ P ⊢ |==> ▷ |==> ∃ z,
      ⌜(a, b) ~l~> (a' z, b' z)⌝ ∗ uPred_ownM (S' z) ∗ Q z) ->
    uPred_ownM S ∗ uPred_ownM r ∗ sqex_support P r ⊢ |==> ▷ |==>
      ∃ z r', uPred_ownM (S' z) ∗ uPred_ownM r' ∗ sqex_support (Q z) r' ∗
        ⌜project γ r' ≡ Some (◯ (b' z))⌝.
  Proof using Type*.
    intros HS Hr Hshape HS' Hupdate.
    eapply sqex_bupd_later_state_retain_core;
      [exact HS | exact Hr | exact Hshape | exact HS' | | exact Hupdate].
    intros n x Hn Hvalid Hlater. destruct n as [|n]; first lia.
    eapply (sqex_later_bupd_authority_from_postN γ
      (sqex_state_update_post a b S' a' b' Q) n x); [ | exact Hvalid | exact Hlater].
    iIntros "(%z & _ & Hstate & _)". iExists (a' z).
    by iApply (sqex_own_project_equiv γ (S' z) (● (a' z)) (HS' z) with "Hstate").
  Qed.
End delayed_update_frame.
