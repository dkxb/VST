(** Semantic frame preservation for sequential basic updates.
    Heap permissions are retained as resources, including affine leftovers. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_frame.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_resource_split.
From iris.algebra Require Import functions view gmap.
From iris.base_logic Require Import bi derived.

Set Default Proof Using "Type".

Section resource_slot.
  Context {Σ : gFunctors} {A : cmra} `{i : !inG Σ A}.

  Definition sqex_erase (γ : gname) (r : iResUR Σ) : iResUR Σ :=
    discrete_fun_insert (inG_id i) (delete γ (r (inG_id i))) r.

  Definition sqex_embed (γ : gname) (a : option A) : iResUR Σ :=
    match a with None => ε | Some a => own.iRes_singleton γ a end.

  Definition sqex_replace (γ : gname) (a : option A) (r : iResUR Σ) : iResUR Σ :=
    sqex_embed γ a ⋅ sqex_erase γ r.

  Global Instance sqex_erase_ne γ : NonExpansive (sqex_erase γ).
  Proof. intros n r s Hrs. unfold sqex_erase. f_equiv; [f_equiv; apply Hrs | exact Hrs]. Qed.

  Global Instance sqex_embed_ne γ : NonExpansive (sqex_embed γ).
  Proof. intros n [a|] [b|] Hab; inversion Hab; simpl; try done.
  apply own.iRes_singleton_ne. assumption. Qed.

  Lemma sqex_erase_op γ r s :
    sqex_erase γ (r ⋅ s) ≡ sqex_erase γ r ⋅ sqex_erase γ s.
  Proof.
    intros j. unfold sqex_erase. rewrite !discrete_fun_lookup_op.
    destruct (decide (j = inG_id i)) as [->|Hne].
    - rewrite !discrete_fun_lookup_insert. intros δ. rewrite lookup_op.
      destruct (decide (δ = γ)) as [->|Hδ].
      + by rewrite !lookup_delete_eq.
      + by rewrite !lookup_delete_ne // lookup_op.
    - by rewrite !discrete_fun_lookup_insert_ne.
  Qed.

  Lemma sqex_erase_validN n γ r : ✓{n} r -> ✓{n} (sqex_erase γ r).
  Proof.
    intros Hr j δ. unfold sqex_erase.
    destruct (decide (j = inG_id i)) as [->|Hj].
    - rewrite discrete_fun_lookup_insert. destruct (decide (δ = γ)) as [->|Hδ].
      + by rewrite lookup_delete_eq.
      + rewrite lookup_delete_ne; [apply Hr | congruence].
    - rewrite discrete_fun_lookup_insert_ne; [apply Hr | done].
  Qed.

  Lemma sqex_project_erase γ r : @sqex_project Σ A i γ (sqex_erase γ r) = None.
  Proof. by rewrite /sqex_project /own.iRes_project /sqex_erase discrete_fun_lookup_insert lookup_delete_eq. Qed.

  Lemma sqex_project_embed γ a : sqex_project γ (sqex_embed γ a) ≡ a.
  Proof.
    destruct a as [a|]; simpl; first apply sqex_project_singleton.
    by rewrite /sqex_project /own.iRes_project lookup_empty.
  Qed.

  Lemma sqex_embed_op γ a b :
    sqex_embed γ (a ⋅ b) ≡ sqex_embed γ a ⋅ sqex_embed γ b.
  Proof.
    destruct a as [a|], b as [b|]; simpl; rewrite ?left_id ?right_id; try done.
    apply own.iRes_singleton_op.
  Qed.

  Lemma sqex_decompose γ r : r ≡ sqex_replace γ (sqex_project γ r) r.
  Proof.
    unfold sqex_replace, sqex_embed, sqex_project, own.iRes_project.
    destruct (r (inG_id i) !! γ) as [a|] eqn:Ha; simpl.
    - rewrite /own.iRes_singleton cmra_transport_trans eq_trans_sym_inv_l /=.
      intros j. rewrite discrete_fun_lookup_op /sqex_erase.
      destruct (decide (j = inG_id i)) as [->|Hj].
      + rewrite discrete_fun_lookup_singleton discrete_fun_lookup_insert.
        intros δ. rewrite lookup_op. destruct (decide (δ = γ)) as [->|Hδ].
        * by rewrite lookup_singleton_eq lookup_delete_eq Ha right_id own.inG_unfold_fold.
        * by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
      + by rewrite discrete_fun_lookup_singleton_ne // discrete_fun_lookup_insert_ne // left_id.
    - rewrite left_id. intros j. unfold sqex_erase.
      destruct (decide (j = inG_id i)) as [->|Hj].
      + rewrite discrete_fun_lookup_insert. intros δ.
        destruct (decide (δ = γ)) as [->|Hδ].
        * by rewrite lookup_delete_eq Ha.
        * by rewrite lookup_delete_ne.
      + by rewrite discrete_fun_lookup_insert_ne.
  Qed.

  Lemma sqex_replace_op_validN n γ a r s :
    ✓{n} (sqex_replace γ a r ⋅ s) <->
    ✓{n} (a ⋅ sqex_project γ s) ∧ ✓{n} (sqex_erase γ r ⋅ sqex_erase γ s).
  Proof.
    rewrite {1}(sqex_decompose γ s) /sqex_replace.
    rewrite (comm op (sqex_embed γ (sqex_project γ s)) (sqex_erase γ s)).
    rewrite -assoc (assoc op (sqex_erase γ r))
      (comm op (sqex_erase γ r ⋅ sqex_erase γ s)) assoc -sqex_embed_op.
    destruct (a ⋅ sqex_project γ s) as [b|] eqn:Hb; simpl.
    - rewrite sqex_singleton_frame_validN sqex_project_op !sqex_project_erase left_id right_id.
      naive_solver.
    - rewrite left_id. naive_solver.
  Qed.

  Lemma sqex_replace_monoN n γ a r :
    sqex_project γ r ≼{n} a -> r ≼{n} sqex_replace γ a r.
  Proof.
    intros [f Hf]. exists (sqex_embed γ f).
    rewrite {2}(sqex_decompose γ r) /sqex_replace.
    rewrite -assoc (comm op (sqex_erase γ r) (sqex_embed γ f)) assoc
      -sqex_embed_op -Hf. done.
  Qed.

  Lemma sqex_project_replace γ a r : sqex_project γ (sqex_replace γ a r) ≡ a.
  Proof. by rewrite /sqex_replace sqex_project_op sqex_project_embed sqex_project_erase right_id. Qed.
End resource_slot.

Section fragment_slot.
  Context {A : ucmra}.

  Definition sqex_fragment_only (b : A) (x : option (authR A)) : Prop :=
    match x with None => b ≡ ε | Some a => a ≡ ◯ b end.

  Lemma sqex_fragment_only_validN n b x y :
    sqex_fragment_only b x ->
    (✓{n} (x ⋅ y) <-> ✓{n} (Some (◯ b) ⋅ y)).
  Proof.
    destruct x as [x|]; simpl.
    - intros ->. done.
    - intros ->. rewrite left_id. destruct y as [y|]; simpl.
      + rewrite -Some_op Some_validN. change (✓{n} y <-> ✓{n} ((ε : authUR A) ⋅ y)).
        by rewrite left_id.
      + change (True <-> ✓{n} (ε : authUR A)).
        split; [intros _; apply ucmra_unit_validN | done].
  Qed.

End fragment_slot.

Section support_semantics.
  Context {Σ : gFunctors}.

  Lemma sqex_support_holds (P : iProp Σ) n r x :
    ✓{n} r -> uPred_holds (sqex_support P r) n x -> uPred_holds P n r.
  Proof.
    rewrite /sqex_support /plainly. uPred.unseal.
    intros Hr Hsupport. specialize (Hsupport n r (Nat.le_refl n)).
    rewrite left_id in Hsupport. apply Hsupport; [done | ].
    change (r ≼{n} r). done.
  Qed.

  Lemma sqex_support_of_holds (P : iProp Σ) n r :
    uPred_holds P n r -> uPred_holds (sqex_support P r) n ε.
  Proof.
    rewrite /sqex_support /plainly. uPred.unseal.
    intros HP k y Hkn Hy Hown. rewrite left_id in Hy. rewrite left_id.
    eapply uPred_mono; eauto.
  Qed.
End support_semantics.

Section auth_frame_cancellation.
  Context {A : ucmra}.

  Lemma sqex_auth_option_cancel_frameN n (a b f : A) (x : option (authR A))
      `{!Cancelable f} :
    a ≡{n}≡ b ⋅ f ->
    ✓{n} (Some (● a) ⋅ x ⋅ Some (◯ f)) -> x ≼{n} Some (◯ b).
  Proof.
    intros Hshape Hvalid. destruct x as [[ag c]|]; simpl.
    - have Hvalid0 : ✓{n} (Some (● a) ⋅ Some (View ag c)).
      { by eapply cmra_validN_op_l. }
      rewrite -Some_op Some_validN in Hvalid0.
      destruct (sqex_auth_full_frame _ _ _ Hvalid0) as [Hag _]. simpl in Hag. subst ag.
      change (✓{n} (Some (● a) ⋅ Some (◯ c) ⋅ Some (◯ f))) in Hvalid.
      rewrite -!Some_op Some_validN -assoc -auth_frag_op auth_both_validN in Hvalid.
      destruct Hvalid as [[d Hd] Ha].
      have Hcancel : f ⋅ b ≡{n}≡ f ⋅ (c ⋅ d).
      { rewrite comm -Hshape Hd. by rewrite -assoc (comm op f d) assoc comm. }
      have Hfb : ✓{n} (f ⋅ b) by rewrite comm -Hshape.
      have Hb : b ≡{n}≡ c ⋅ d by apply (cancelableN f).
      exists (Some (◯ d)). rewrite -Some_op -auth_frag_op. by rewrite Hb.
    - exists (Some (◯ b)). by rewrite left_id.
  Qed.
End auth_frame_cancellation.

Section concrete_heap_support.
  Context `{!lrSqGS Σ}.
  Local Existing Instance lr_ext_specs.

  Lemma sqex_state_heap_project m p hF :
    sq_heap_name ≠ sq_freeable_name ->
    @sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name
      (sqex_state_resource m p hF) ≡ Some (● sq_heap_cells m p).
  Proof.
    intros Hnames. rewrite /sqex_state_resource /sqex_heap_resource
      sqex_project_op sqex_project_singleton sqex_project_other_name // right_id.
  Qed.

  Lemma sqex_exact_fragment_only m p hF r :
    sq_heap_cells m p ≡ sqex_heap_fragment r ->
    sqex_resource_fits m p hF r ⊢
      ⌜sqex_fragment_only (sq_heap_cells m p)
        (@sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r)⌝.
  Proof.
    intros Hexact. rewrite /sqex_resource_fits. sbi_unfold=> n Hvalid.
    destruct (sqex_heap_projection_shapeN n m p hF r Hvalid) as [Hnone|[h Hsome]].
    - rewrite /sqex_fragment_only Hnone.
      by rewrite /sqex_heap_fragment Hnone /sqex_auth_fragment in Hexact.
    - rewrite /sqex_fragment_only Hsome.
      rewrite /sqex_heap_fragment Hsome /sqex_auth_fragment /= in Hexact.
      by rewrite Hexact.
  Qed.

  Lemma sqex_heap_projection_exact m p r :
    @sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r ≡
      Some (◯ sq_heap_cells m p) ->
    sq_heap_cells m p ≡ sqex_heap_fragment r.
  Proof.
    intros Hproject. rewrite /sqex_heap_fragment /sqex_auth_fragment.
    destruct (@sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r)
      as [x|]; last inversion Hproject.
    apply Some_equiv_inj in Hproject. by rewrite Hproject.
  Qed.

  Lemma sqex_exact_witness_intro m total hF p (r : iResUR Σ) e (Φ : sq_val -> iProp Σ) :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p ->
    sq_heap_cells m p ≡ sqex_heap_fragment r ->
    uPred_ownM (sqex_state_resource m total hF) -∗ uPred_ownM r -∗
    sqex_support (EXWP e {{ v, Φ v }}) r -∗
    uPred_ownM (sqex_state_resource m total hF) ∗
      sqex_exact_thread_inv m hF (SqexThread e p Φ).
  Proof.
    intros Hnames Hrel Hexact. iIntros "Hstate Hr #Hsupport".
    iDestruct (sqex_resource_fits_intro with "Hstate Hr") as "#Hfits".
    iDestruct (sqex_state_projection _ _ _ _ Hnames with "Hfits") as "[_ Hlocal]".
    have Hp := sqex_resource_permissions_exact _ _ _ Hrel Hexact.
    rewrite -Hp. iFrame "Hstate". iExists r. iFrame "Hr Hsupport Hlocal". done.
  Qed.
End concrete_heap_support.
