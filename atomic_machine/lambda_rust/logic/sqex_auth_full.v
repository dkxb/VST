(** Full ownership of an authoritative slot cannot first appear through a
    basic update: a discarded-authority frame rules out every other case. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_resources.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_resource_split.
From iris.algebra Require Import auth view dfrac agree.
From iris.base_logic Require Import bi derived.

Set Default Proof Using "Type*".

Lemma sqex_dfrac_nonfull_discarded (dq : dfrac) :
  ✓ dq -> dq ≠ DfracOwn 1 -> ✓ (dq ⋅ DfracDiscarded).
Proof.
  destruct dq as [q| |q]; simpl; try done.
  intros Hq Hne. change (q ≤ 1)%Qp in Hq.
  change (q < 1)%Qp. apply Qp.le_lteq in Hq as [Hlt|Heq]; first done.
  exfalso. apply Hne. by rewrite Heq.
Qed.

Section authority_shape.
  Context {A : ucmra} `{!CmraDiscrete A}.

  Lemma sqex_auth_full_or_discardedN n (x : option (authR A)) :
    ✓{n} x ->
    (exists a b, x ≡ Some (● a ⋅ ◯ b)) \/
    (exists a, ✓{n} (x ⋅ Some (●□ a))).
  Proof.
    destruct x as [[[[dq ag]|] b]|]; simpl.
    - intros Hvalid. rewrite Some_validN view.view_validN_eq /= in Hvalid.
      destruct Hvalid as [Hdq [a [Hag Hab]]].
      have Hag' : ag ≡ to_agree a.
      { apply (discrete_iff n ag (to_agree a)). exact Hag. }
      have Hrep : View (Some (dq, ag)) b ≡ (●{dq} a ⋅ ◯ b : authR A).
      { rewrite /auth_auth /auth_frag /view_auth /view_frag view.view_op_eq /=
          right_id left_id. split; [by rewrite Hag' | done]. }
      destruct (decide (dq = DfracOwn 1)) as [->|Hne].
      + left. exists a, b. by rewrite Hrep.
      + right. exists a. rewrite Hrep -Some_op Some_validN.
        rewrite -assoc (comm op (◯ b) (●□ a)) assoc -auth_auth_dfrac_op.
        apply auth_both_dfrac_validN. split.
        * apply sqex_dfrac_nonfull_discarded; last done.
          by apply (cmra_discrete_valid_iff n).
        * exact Hab.
    - intros Hvalid. right. exists b.
      change (✓{n} (Some (◯ b))) in Hvalid.
      rewrite Some_validN auth_frag_validN in Hvalid.
      change (✓{n} (Some (◯ b) ⋅ Some (●□ b))).
      rewrite -Some_op Some_validN comm auth_both_dfrac_validN.
      split; first done. split; first done. exact Hvalid.
    - intros _. right. exists (ε : A). rewrite left_id Some_validN auth_auth_dfrac_validN.
      split; [done | apply ucmra_unit_validN].
  Qed.

  Lemma sqex_auth_full_discarded_invalidN n (a b : A) :
    ¬ ✓{n} (Some (● a) ⋅ Some (●□ b)).
  Proof.
    rewrite -Some_op Some_validN auth_auth_dfrac_op_validN.
    intros [Hbad _]. exact (exclusiveN_l n (DfracOwn 1) DfracDiscarded Hbad).
  Qed.
End authority_shape.

Section forcing_authority.
  Context {Σ : gFunctors} {A : ucmra} `{!CmraDiscrete A, i : !inG Σ (authR A)}.
  Local Notation project := (@sqex_project Σ (authR A) i).

  Lemma sqex_bupd_full_authorityN γ n r :
    ✓{n} r ->
    uPred_holds (|==> ∃ a : A, own γ (● a))%I n r ->
    exists a b, project γ r ≡ Some (● a ⋅ ◯ b).
  Proof.
    intros Hr Hupd.
    have Hproject := @sqex_project_validN Σ (authR A) i n γ r Hr.
    destruct (sqex_auth_full_or_discardedN n (project γ r) Hproject)
      as [Hfull|[a Hdiscard]]; first done.
    exfalso.
    have Hframe : ✓{n} (r ⋅ own.iRes_singleton γ (●□ a)).
    { rewrite comm sqex_singleton_frame_validN. split; first done.
      by rewrite comm. }
    revert Hupd. rewrite own.own_eq /own.own_def. uPred.unseal.
    intros Hupd. destruct (Hupd n (own.iRes_singleton γ (●□ a)) (Nat.le_refl n) Hframe)
      as (out & Hout & b & Hb).
    have Hbad : ✓{n} (own.iRes_singleton γ (● b) ⋅ own.iRes_singleton γ (●□ a)).
    { eapply cmra_validN_includedN; first exact Hout.
      apply cmra_monoN_r. exact Hb. }
    rewrite sqex_singleton_frame_validN sqex_project_singleton in Hbad.
    by apply (sqex_auth_full_discarded_invalidN n b a), Hbad.
  Qed.

  Lemma sqex_bupd_authority_from_postN γ (P : iProp Σ) n r :
    (P ⊢ ∃ a : A, own γ (● a)) -> ✓{n} r ->
    uPred_holds (|==> P)%I n r ->
    exists a b, project γ r ≡ Some (● a ⋅ ◯ b).
  Proof.
    intros HP Hr Hupd. apply (sqex_bupd_full_authorityN γ n r); first done.
    have [Hmono] := bupd_mono P (∃ a : A, own γ (● a))%I HP.
    by apply Hmono.
  Qed.

  Lemma sqex_later_bupd_authority_from_postN γ (P : iProp Σ) n r :
    (P ⊢ ∃ a : A, own γ (● a)) -> ✓{S n} r ->
    uPred_holds (▷ |==> P)%I (S n) r ->
    exists a b, project γ r ≡ Some (● a ⋅ ◯ b).
  Proof.
    intros HP Hr. uPred.unseal. simpl. intros Hlater.
    apply (sqex_bupd_authority_from_postN γ P n r HP).
    - exact (cmra_validN_le (S n) n r Hr (Nat.le_succ_diag_r n)).
    - uPred.unseal. exact Hlater.
  Qed.
End forcing_authority.
