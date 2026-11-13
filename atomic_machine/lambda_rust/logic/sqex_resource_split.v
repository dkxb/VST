(** Recovering exact heap permission maps from separated WP resources. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pool.
From iris.algebra Require Import functions view gmap.

Set Default Proof Using "Type".
Local Existing Instance lr_ext_specs.

Lemma sqex_singleton_other_name {Σ : gFunctors} (i j : gid Σ)
    (γ γ' : gname) (a : rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)) :
  γ ≠ γ' ->
  (discrete_fun_singleton i {[γ' := a]} : iResUR Σ) j !! γ = None.
Proof.
  intros Hne. unfold discrete_fun_singleton, discrete_fun_insert.
  destruct (decide (i = j)) as [Heq|Hne']; last done.
  destruct Heq. by rewrite lookup_singleton_ne.
Qed.

Section projection.
  Context {Σ : gFunctors} {A : cmra} `{i : !inG Σ A}.

  Definition sqex_project (γ : gname) (r : iResUR Σ) : option A :=
    own.iRes_project γ r.

  Global Instance sqex_project_ne γ : NonExpansive (sqex_project γ).
  Proof. apply own.iRes_project_ne. Qed.

  Lemma sqex_project_op γ r s :
    sqex_project γ (r ⋅ s) ≡ sqex_project γ r ⋅ sqex_project γ s.
  Proof. apply own.iRes_project_op. Qed.

  Lemma sqex_project_singleton γ a :
    sqex_project γ (own.iRes_singleton γ a) ≡ Some a.
  Proof. apply own.iRes_project_singleton. Qed.

  Lemma sqex_project_other_name {B : cmra} `{!inG Σ B} γ γ' (b : B) :
    γ ≠ γ' -> sqex_project γ (own.iRes_singleton γ' b) = None.
  Proof.
    intros Hne. unfold sqex_project, own.iRes_project, own.iRes_singleton.
    by rewrite sqex_singleton_other_name.
  Qed.

  Lemma sqex_project_validN n γ r : ✓{n} r -> ✓{n} (sqex_project γ r).
  Proof.
    intros Hr. unfold sqex_project, own.iRes_project.
    have Hvalid := Hr (inG_id i).
    have Hv := Hvalid γ.
    destruct (r (inG_id i) !! γ) as [a|] eqn:Ha; simpl in *; last done.
    rewrite Some_validN cmra_transport_validN.
    apply cmra_morphism_validN.
    - unfold own.inG_fold. apply _.
    - by rewrite Ha in Hv.
  Qed.

  Lemma sqex_project_validN_iff n γ r :
    ✓{n} (sqex_project γ r) <-> ✓{n} (r (inG_id i) !! γ).
  Proof.
    unfold sqex_project, own.iRes_project.
    destruct (r (inG_id i) !! γ) as [a|]; simpl; last done.
    rewrite !Some_validN cmra_transport_validN.
    rewrite -(own.inG_unfold_validN n (own.inG_fold a)) own.inG_unfold_fold.
    done.
  Qed.

  Lemma sqex_singleton_frame_validN n γ a r :
    ✓{n} (own.iRes_singleton γ a ⋅ r) <->
      ✓{n} r ∧ ✓{n} (Some a ⋅ sqex_project γ r).
  Proof.
    split.
    - intros Hvalid. split; first by eapply cmra_validN_op_r.
      have Hp := sqex_project_validN n γ _ Hvalid.
      by rewrite sqex_project_op sqex_project_singleton in Hp.
    - intros [Hr Hp] j δ.
      destruct (decide (j = inG_id i)) as [->|Hj].
      + destruct (decide (δ = γ)) as [->|Hδ].
        * rewrite -sqex_project_validN_iff sqex_project_op sqex_project_singleton. done.
        * rewrite /own.iRes_singleton discrete_fun_lookup_op discrete_fun_lookup_singleton
            lookup_op lookup_singleton_ne; last congruence.
          rewrite left_id. exact (Hr (inG_id i) δ).
      + rewrite /own.iRes_singleton discrete_fun_lookup_op discrete_fun_lookup_singleton_ne // left_id.
        exact (Hr j δ).
  Qed.

  Lemma sqex_own_project γ r a :
    sqex_project γ r = Some a -> uPred_ownM r ⊢ own γ a.
  Proof.
    intros Ha. rewrite own.own_eq.
    apply uPred.ownM_mono. by apply own.iRes_project_below.
  Qed.
End projection.

Section auth_projection.
  Context {A : ucmra}.

  Definition sqex_auth_fragment (x : option (authR A)) : A :=
    match x with None => ε | Some a => view_frag_proj a end.

  Global Instance sqex_auth_fragment_ne : NonExpansive sqex_auth_fragment.
  Proof.
    intros n [x|] [y|] Hxy; simpl; inversion Hxy; subst; try done.
    by apply view_frag_proj_ne.
  Qed.

  Global Instance sqex_auth_fragment_proper :
    Proper ((≡) ==> (≡)) sqex_auth_fragment := ne_proper _.

  Lemma sqex_auth_fragment_op x y :
    sqex_auth_fragment (x ⋅ y) ≡ sqex_auth_fragment x ⋅ sqex_auth_fragment y.
  Proof.
    destruct x as [x|], y as [y|]; simpl; rewrite ?left_id ?right_id; try done.
  Qed.

  Lemma sqex_auth_full_frame n (a : A) (x : authR A) :
    ✓{n} (● a ⋅ x) ->
    view_auth_proj x = None ∧ view_frag_proj x ≼{n} a ∧ ✓{n} a.
  Proof.
    destruct x as [[[dq ag]|] b].
    - rewrite /auth_auth /view_auth view.view_op_eq view.view_validN_eq /=.
      intros [Hbad _]. exfalso. exact (exclusiveN_l n (DfracOwn 1) dq Hbad).
    - intros Hvalid. split; first done.
      apply auth_both_validN. exact Hvalid.
  Qed.

  Lemma sqex_auth_option_frame n (a : A) x :
    ✓{n} (Some (● a) ⋅ x) ->
    sqex_auth_fragment x ≼{n} a ∧ ✓{n} a.
  Proof.
    destruct x as [x|]; simpl.
    - rewrite -Some_op Some_validN. intros Hvalid.
      exact (proj2 (sqex_auth_full_frame _ _ _ Hvalid)).
    - rewrite right_id Some_validN auth_auth_validN.
      intros Ha. split; last done. apply ucmra_unit_leastN.
  Qed.
  Lemma sqex_auth_option_shrink n (a : A) x :
    ✓{n} (Some (● a) ⋅ x) ->
    ✓{n} (Some (● (sqex_auth_fragment x)) ⋅ x).
  Proof.
    destruct x as [[ag b]|]; simpl.
    - rewrite -!Some_op !Some_validN.
      intros Hvalid. destruct (sqex_auth_full_frame _ _ _ Hvalid) as [Hag [Hinc Ha]].
      simpl in Hag. subst ag. change (✓{n} (● b ⋅ ◯ b)).
      apply auth_both_validN. split; first done.
      by eapply cmra_validN_includedN.
    - rewrite !right_id !Some_validN !auth_auth_validN. intros _.
      apply ucmra_unit_validN.
  Qed.
End auth_projection.

Section heap_projection.
  Context `{!sq_heapGS Σ}.

  Definition sqex_heap_fragment (r : iResUR Σ) : sq_heapUR :=
    sqex_auth_fragment (@sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r).

  Definition sqex_resource_permissions (r : iResUR Σ) : perm_map :=
    sqex_fragment_permissions (sqex_heap_fragment r).

  Global Instance sqex_heap_fragment_ne : NonExpansive sqex_heap_fragment.
  Proof. solve_proper. Qed.

  Global Instance sqex_heap_fragment_proper :
    Proper ((≡) ==> (≡)) sqex_heap_fragment := ne_proper _.

  Lemma sqex_heap_fragment_op r s :
    sqex_heap_fragment (r ⋅ s) ≡ sqex_heap_fragment r ⋅ sqex_heap_fragment s.
  Proof. by rewrite /sqex_heap_fragment sqex_project_op sqex_auth_fragment_op. Qed.

  Lemma sqex_heap_fragment_unit : sqex_heap_fragment (ε : iResUR Σ) = ε.
  Proof. done. Qed.

  Global Instance sqex_heap_fragment_hom :
    MonoidHomomorphism op op (≡) sqex_heap_fragment.
  Proof. split; [split|]; try apply _; [apply sqex_heap_fragment_op | by rewrite sqex_heap_fragment_unit]. Qed.

  Lemma sqex_heap_fragment_big_opM {K A} `{Countable K}
      (f : K -> A -> iResUR Σ) (R : gmap K A) :
    sqex_heap_fragment ([^op map] k ↦ r ∈ R, f k r) ≡
      [^op map] k ↦ r ∈ R, sqex_heap_fragment (f k r).
  Proof. apply big_opM_commute, sqex_heap_fragment_hom. Qed.

  Lemma sqex_state_projectionN n m p hF r :
    sq_heap_name ≠ sq_freeable_name ->
    ✓{n} (sqex_state_resource m p hF ⋅ r) ->
    sq_heap_rel m (sqex_resource_permissions r) ∧
    sq_heap_cells m (sqex_resource_permissions r) ≡ sqex_heap_fragment r ∧
    sqex_heap_fragment r ≼ sq_heap_cells m p ∧
    ✓{n} (sqex_state_resource m (sqex_resource_permissions r) hF ⋅ r).
  Proof.
    intros Hnames Hvalid.
    rewrite /sqex_state_resource /sqex_heap_resource -assoc
      sqex_singleton_frame_validN in Hvalid.
    destruct Hvalid as [Hframe Hproject].
    rewrite sqex_project_op sqex_project_other_name // left_id in Hproject.
    have Hinc := proj1 (sqex_auth_option_frame _ _ _ Hproject).
    have Hinc' : sqex_heap_fragment r ≼ sq_heap_cells m p.
    { apply (cmra_discrete_included_iff n). exact Hinc. }
    destruct (sqex_fragment_representation _ _ _ Hinc') as [Hrel Hcells].
    split; first exact Hrel. split; first exact Hcells. split; first done.
    rewrite /sqex_state_resource /sqex_heap_resource -assoc
      sqex_singleton_frame_validN. split; first done.
    rewrite sqex_project_op sqex_project_other_name // left_id Hcells.
    by apply sqex_auth_option_shrink in Hproject.
  Qed.

  Lemma sqex_heap_projection_shapeN n m p hF r :
    ✓{n} (sqex_state_resource m p hF ⋅ r) ->
    @sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r = None ∨
      exists h, @sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r = Some (◯ h).
  Proof.
    intros Hvalid.
    have Hv : ✓{n} (sqex_heap_resource m p ⋅ r).
    { apply (cmra_validN_op_l n _ (own.iRes_singleton sq_freeable_name (● hF))).
      rewrite -assoc (comm op r) assoc. exact Hvalid. }
    rewrite /sqex_heap_resource sqex_singleton_frame_validN in Hv.
    destruct Hv as [_ Hp].
    destruct (@sqex_project Σ (authR sq_heapUR) sq_heap_inG sq_heap_name r)
      as [[ag h]|] eqn:Hproject; last by left.
    right. rewrite Hproject -Some_op Some_validN in Hp.
    have Ha := proj1 (sqex_auth_full_frame _ _ _ Hp).
    simpl in Ha. subst ag. by exists h.
  Qed.

  Lemma sqex_state_projection m p hF r :
    sq_heap_name ≠ sq_freeable_name ->
    ✓ (sqex_state_resource m p hF ⋅ r) ⊢
      ⌜sq_heap_rel m (sqex_resource_permissions r) ∧
        sq_heap_cells m (sqex_resource_permissions r) ≡ sqex_heap_fragment r ∧
        sqex_heap_fragment r ≼ sq_heap_cells m p⌝ ∧
      sqex_resource_fits m (sqex_resource_permissions r) hF r.
  Proof.
    intros Hnames. rewrite /sqex_resource_fits.
    sbi_unfold=> n. intros Hvalid.
    destruct (sqex_state_projectionN _ _ _ _ _ Hnames Hvalid) as [Hr [Hc [Hi Hv]]].
    naive_solver.
  Qed.
End heap_projection.

Lemma sqex_heap_fragment_absorb (h H : sq_heapUR) :
  h ⋅ H ≼ H -> h = ∅.
Proof.
  intros Hinc. apply (map_eq (M := gmap loc)). intros l. rewrite lookup_empty.
  destruct (h !! l) as [[q a]|] eqn:Hh; last done.
  exfalso. have Hl := proj1 (lookup_included _ _) Hinc l.
  rewrite lookup_op Hh in Hl.
  destruct (H !! l) as [[q' a']|] eqn:HH; rewrite HH /= in Hl.
  - rewrite -Some_op in Hl. apply Some_included in Hl as [[Hq _]|Hpart].
    + change (q + q' = q')%Qp in Hq. apply (Qp.not_add_le_r q q'). by rewrite Hq.
    + apply pair_included in Hpart as [Hq _].
      apply (Qp.not_add_le_r q q'). by apply frac_included_weak.
  - by apply (Some_included_is_Some _ _) in Hl.
Qed.

Lemma sqex_fragment_permissions_equiv (h h' : sq_heapUR) :
  h ≡ h' -> sqex_fragment_permissions h = sqex_fragment_permissions h'.
Proof.
  intros Heq. apply (map_eq (M := gmap loc)). intros l.
  rewrite /sqex_fragment_permissions !lookup_fmap.
  specialize (Heq l). destruct (h !! l) as [[q a]|] eqn:Hh;
    destruct (h' !! l) as [[q' a']|] eqn:Hh';
    rewrite Hh Hh' in Heq; rewrite Hh Hh' /=; try done; inversion Heq; subst.
  f_equal. exact (proj1 H1).
Qed.

Lemma sqex_fragment_permissions_cells m p :
  sq_heap_rel m p -> sqex_fragment_permissions (sq_heap_cells m p) = p.
Proof.
  intros Hrel. apply (map_eq (M := gmap loc)). intros l.
  rewrite /sqex_fragment_permissions lookup_fmap sq_heap_cells_lookup.
  destruct (p !! l) as [q|] eqn:Hp; rewrite Hp /=; last done.
  have Hl : is_Some (m !! l).
  { apply (proj1 (elem_of_dom (M := gmap loc) (D := gset loc) m l)), Hrel.
    exact (elem_of_dom_2 (M := gmap loc) p l q Hp). }
  destruct Hl as [v Hv]. by rewrite Hv.
Qed.

Lemma sqex_resource_permissions_exact `{!sq_heapGS Σ} m p r :
  sq_heap_rel m p -> sq_heap_cells m p ≡ sqex_heap_fragment r ->
  p = sqex_resource_permissions r.
Proof.
  intros Hrel Heq. rewrite -(sqex_fragment_permissions_cells m p Hrel).
  by apply sqex_fragment_permissions_equiv.
Qed.

Global Instance sqex_heap_cancelable (h : sq_heapUR) : Cancelable h.
Proof.
  apply gmap_cancelable.
  - intros [q a]. apply _.
  - intros [q a]. apply _.
Qed.

Section collection_support.
  Context {Σ : gFunctors}.

  Lemma sqex_support_big_sepM_with {A} (C : gmap nat A)
      (W : nat -> A -> iProp Σ) (K : nat -> A -> iResUR Σ -> Prop) :
    ([∗ map] i ↦ c ∈ C, ∃ r, uPred_ownM r ∗ sqex_support (W i c) r ∗ ⌜K i c r⌝) ⊢
    ∃ R : gmap nat (iResUR Σ),
      uPred_ownM ([^op map] r ∈ R, r) ∗
      ([∗ map] i ↦ c; r ∈ C; R, sqex_support (W i c) r) ∗
      ⌜forall i c r, C !! i = Some c -> R !! i = Some r -> K i c r⌝.
  Proof.
    induction C as [|i c C Hfresh IH] using map_ind.
    - rewrite big_sepM_empty. iIntros "_". iExists ∅.
      rewrite big_opM_empty big_sepM2_empty uPred.ownM_unit'.
      iSplit; first done. iSplit; first done. iPureIntro.
      intros j d r Hj. by rewrite lookup_empty in Hj.
    - rewrite big_sepM_insert //. iIntros "[(%r & Hr & #Hsupport & %HK) HC]".
      iDestruct (IH with "HC") as (R) "(HR & #Hsupports & %HKS)".
      iDestruct (big_sepM2_dom with "Hsupports") as %Hdom.
      have HfreshR : R !! i = None.
      { apply (not_elem_of_dom (D := gset nat)). rewrite -Hdom.
        by apply (not_elem_of_dom (D := gset nat)). }
      iExists (<[i := r]> R). rewrite big_opM_insert // uPred.ownM_op.
      iFrame "Hr HR". iSplit.
      { rewrite big_sepM2_insert //. by iFrame "Hsupport Hsupports". }
      iPureIntro. intros j d s Hd Hs.
      destruct (decide (i = j)) as [<-|Hne].
      + rewrite !lookup_insert_eq in Hd Hs. inversion Hd; inversion Hs; subst. done.
      + rewrite !lookup_insert_ne // in Hd Hs. by eapply HKS.
  Qed.
End collection_support.

Definition sqex_rebuild_threads `{!sq_heapGS Σ}
    (C : sqex_threads Σ) (R : gmap nat (iResUR Σ)) : sqex_threads Σ :=
  map_zip_with (fun c r => SqexThread (sqex_thread_expr c)
    (sqex_resource_permissions r) (sqex_thread_post c)) C R.

Definition sqex_thread_shapes {Σ} (C : sqex_threads Σ) :=
  (fun c => (sqex_thread_expr c, sqex_thread_post c)) <$> C.

Lemma sqex_rebuild_threads_shapes `{!sq_heapGS Σ} C R :
  dom C = (dom R : gset nat) ->
  sqex_thread_shapes (sqex_rebuild_threads C R) = sqex_thread_shapes C.
Proof.
  intros Hdom. apply (map_eq (M := gmap nat)). intros i.
  rewrite /sqex_thread_shapes /sqex_rebuild_threads !lookup_fmap map_lookup_zip_with.
  destruct (C !! i) as [c|] eqn:Hc; rewrite Hc /=; last done.
  have Hi : i ∈ (dom R : gset nat).
  { rewrite -Hdom. exact (elem_of_dom_2 (M := gmap nat) C i c Hc). }
  apply elem_of_dom in Hi as [r Hr]. by rewrite Hr.
Qed.

Lemma sqex_rebuild_threads_cells `{!sq_heapGS Σ} m C R :
  dom C = (dom R : gset nat) ->
  sqex_threads_cells m (sqex_rebuild_threads C R) ≡
    [^op map] r ∈ R, sq_heap_cells m (sqex_resource_permissions r).
Proof.
  intros Hdom. rewrite /sqex_threads_cells /sqex_rebuild_threads
    map_zip_with_map_zip big_opM_fmap /=.
  trans ([^op map] cr ∈ map_zip C R, sq_heap_cells m (sqex_resource_permissions cr.2)).
  { apply (big_opM_proper (M := sq_heapUR)). intros i [c r] Hi. done. }
  rewrite -(big_opM_fmap snd (fun _ r => sq_heap_cells m (sqex_resource_permissions r))).
  rewrite snd_map_zip; first done.
  intros i Hi. apply elem_of_dom. rewrite Hdom. by apply elem_of_dom.
Qed.

Lemma sqex_rebuild_threads_coherentN `{!sq_heapGS Σ} n m p hF C R :
  sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p ->
  dom C = (dom R : gset nat) ->
  ✓{n} (sqex_state_resource m p hF ⋅ ([^op map] r ∈ R, r)) ->
  sqex_threads_coherent m p (sqex_rebuild_threads C R).
Proof.
  intros Hnames Hrel Hdom Hvalid.
  have Hlocal : forall i r, R !! i = Some r ->
      sq_heap_rel m (sqex_resource_permissions r) ∧
      sq_heap_cells m (sqex_resource_permissions r) ≡ sqex_heap_fragment r.
  { intros i r Hr. destruct (sqex_state_projectionN n m p hF r Hnames) as [Hrelr [Hcellsr _]].
    - apply (cmra_validN_op_l n _ ([^op map] r ∈ delete i R, r)).
      by rewrite -assoc -(big_opM_delete _ R i r Hr).
    - done. }
  destruct (sqex_state_projectionN _ _ _ _ _ Hnames Hvalid) as [_ [_ [Hinc _]]].
  have Hauth : ✓ (sq_heap_cells m p).
  { have Hv := cmra_validN_op_l _ _ _ Hvalid.
    rewrite /sqex_state_resource in Hv.
    have Hv' := cmra_validN_op_l _ _ _ Hv.
    apply (cmra_discrete_valid_iff n).
    have Hp := @sqex_project_validN Σ (authR sq_heapUR) (@sq_heap_inG Σ sq_heapGS0) n (@sq_heap_name Σ sq_heapGS0) _ Hv'.
    rewrite /sqex_heap_resource in Hp.
    rewrite sqex_project_singleton Some_validN auth_auth_validN in Hp.
    exact Hp. }
  split; first done. split; first done. split.
  - rewrite sqex_rebuild_threads_cells //.
    rewrite sqex_heap_fragment_big_opM in Hinc.
    have Heq : ([^op map] r ∈ R, sq_heap_cells m (sqex_resource_permissions r)) ≡
        ([^op map] r ∈ R, sqex_heap_fragment r).
    { apply (big_opM_proper (M := sq_heapUR)). intros i r Hr.
      exact (proj2 (Hlocal _ _ Hr)). }
    by rewrite Heq.
  - intros i c Hc. unfold sqex_rebuild_threads in Hc. apply (map_lookup_zip_with_Some (M := gmap nat)) in Hc as (c0 & r & -> & Hc0 & Hr).
    exact (proj1 (Hlocal _ _ Hr)).
Qed.

Lemma sqex_rebuild_threads_coherent `{!sq_heapGS Σ} m p hF C R :
  sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p ->
  dom C = (dom R : gset nat) ->
  ✓ (sqex_state_resource m p hF ⋅ ([^op map] r ∈ R, r)) ⊢@{iPropI Σ}
    ⌜sqex_threads_coherent m p (sqex_rebuild_threads C R)⌝.
Proof.
  intros Hnames Hrel Hdom. sbi_unfold=> n Hvalid.
  by eapply sqex_rebuild_threads_coherentN.
Qed.

Lemma sqex_state_projection_member `{!sq_heapGS Σ} m p hF (R : gmap nat (iResUR Σ)) i r :
  sq_heap_name ≠ sq_freeable_name -> R !! i = Some r ->
  ✓ (sqex_state_resource m p hF ⋅ ([^op map] r ∈ R, r)) ⊢
    ⌜sq_heap_rel m (sqex_resource_permissions r) ∧
      sq_heap_cells m (sqex_resource_permissions r) ≡ sqex_heap_fragment r⌝ ∧
    sqex_resource_fits m (sqex_resource_permissions r) hF r.
Proof.
  intros Hnames Hr. rewrite /sqex_resource_fits. sbi_unfold=> n Hvalid.
  have Hv : ✓{n} (sqex_state_resource m p hF ⋅ r).
  { apply (cmra_validN_op_l n _ ([^op map] r ∈ delete i R, r)).
    by rewrite -assoc -(big_opM_delete _ R i r Hr). }
  destruct (sqex_state_projectionN _ _ _ _ _ Hnames Hv) as [Hrel [Hcells [_ Hfit]]].
  naive_solver.
Qed.

Lemma sqex_own_big_opM {Σ : gFunctors} (R : gmap nat (iResUR Σ)) :
  uPred_ownM ([^op map] r ∈ R, r) ⊣⊢ [∗ map] r ∈ R, uPred_ownM r.
Proof. apply big_opM_commute, uPred.uPred_ownM_sep_homomorphism. Qed.

Section exact_threads.
  Context `{!lrSqGS Σ}.

  Definition sqex_exact_thread_inv m hF (c : sqex_thread Σ) : iProp Σ :=
    ∃ r : iResUR Σ, uPred_ownM r ∗
      sqex_support (EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}) r ∗
      ⌜sq_heap_cells m (sqex_thread_perm c) ≡ sqex_heap_fragment r⌝ ∗
      sqex_resource_fits m (sqex_thread_perm c) hF r.

  Definition sqex_exact_threads_inv m hF (C : sqex_threads Σ) : iProp Σ :=
    [∗ map] c ∈ C, sqex_exact_thread_inv m hF c.

  Lemma sqex_exact_thread_inv_forget m hF c :
    sqex_exact_thread_inv m hF c ⊢ sqex_thread_inv m hF c.
  Proof. iIntros "(%r & Hr & Hsupport & _ & Hfits)". iExists r. by iFrame. Qed.

  Lemma sqex_threads_reconstruct_resources m p hF (C : sqex_threads Σ)
      (R : gmap nat (iResUR Σ)) :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    uPred_ownM ([^op map] r ∈ R, r) -∗
    ([∗ map] i ↦ c; r ∈ C; R,
      sqex_support (EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}) r) -∗
    ⌜sqex_threads_coherent m p (sqex_rebuild_threads C R)⌝ ∗
      uPred_ownM (sqex_state_resource m p hF) ∗
      sqex_exact_threads_inv m hF (sqex_rebuild_threads C R).
  Proof.
    intros Hnames Hrel. iIntros "Hstate HR #Hsupports".
    iDestruct (big_sepM2_dom with "Hsupports") as %Hdom.
    iAssert (✓ (sqex_state_resource m p hF ⋅ ([^op map] r ∈ R, r)))%I
      with "[Hstate HR]" as "#Hvalid".
    { iApply uPred.ownM_valid. rewrite uPred.ownM_op. iFrame. }
    iDestruct (sqex_rebuild_threads_coherent _ _ _ _ _ Hnames Hrel Hdom with "Hvalid")
      as %Hcoherent.
    iSplit; first done.
    iFrame "Hstate".
    rewrite /sqex_exact_threads_inv /sqex_rebuild_threads map_zip_with_map_zip big_sepM_fmap.
    iEval (rewrite sqex_own_big_opM) in "HR".
    have Hlookup : forall i, is_Some (R !! i) -> is_Some (C !! i).
    { intros i Hi. apply (proj1 (elem_of_dom (M := gmap nat) (D := gset nat) C i)).
      rewrite Hdom. by apply elem_of_dom. }
    have HownR : ([∗ map] r ∈ R, uPred_ownM r) ⊣⊢
        ([∗ map] cr ∈ map_zip C R, uPred_ownM cr.2).
    { by rewrite -(big_sepM_fmap snd (fun _ r => uPred_ownM r)) (snd_map_zip C R Hlookup). }
    iEval (rewrite HownR) in "HR".
    iApply (big_sepM_impl with "HR"). iIntros "!>" (i [c r] Hcr) "Hr".
    apply map_lookup_zip_Some in Hcr as [Hc Hr]. simpl.
    iDestruct (big_sepM2_lookup _ _ _ _ _ _ Hc Hr with "Hsupports") as "Hsupport".
    iDestruct (sqex_state_projection_member _ _ _ _ _ _ Hnames Hr with "Hvalid")
      as "[[%Hrelr %Hcells] Hfit]".
    iExists r. simpl. iFrame "Hr Hsupport Hfit". done.
  Qed.

  Lemma sqex_threads_reconstruct_mixed m p hF (C : sqex_threads Σ) (F : gset nat) :
    sq_heap_name ≠ sq_freeable_name -> sq_heap_rel m p ->
    (forall i c, C !! i = Some c -> i ∈ F -> sq_heap_rel m (sqex_thread_perm c)) ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    ([∗ map] i ↦ c ∈ C,
      if decide (i ∈ F) then sqex_exact_thread_inv m hF c
      else EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}) -∗
    ∃ C' : sqex_threads Σ,
      ⌜sqex_thread_shapes C' = sqex_thread_shapes C ∧
        sqex_threads_coherent m p C' ∧
        (forall i, i ∈ F -> C' !! i = C !! i)⌝ ∗
      uPred_ownM (sqex_state_resource m p hF) ∗ sqex_exact_threads_inv m hF C'.
  Proof.
    intros Hnames Hrel Hfixedrel. iIntros "Hstate Hthreads".
    iAssert ([∗ map] i ↦ c ∈ C, ∃ r, uPred_ownM r ∗
      sqex_support (EXWP (sqex_thread_expr c) {{ v, sqex_thread_post c v }}) r ∗
      ⌜i ∈ F -> sqex_thread_perm c = sqex_resource_permissions r⌝)%I
      with "[Hthreads]" as "Hthreads".
    { iApply (big_sepM_impl with "Hthreads"). iIntros "!>" (i c Hc) "Hthread".
      destruct (decide (i ∈ F)) as [Hi|Hi].
      - iDestruct "Hthread" as (r) "(Hr & Hsupport & %Hcells & _)".
        iExists r. iFrame. iPureIntro. intros _.
        by eapply sqex_resource_permissions_exact, Hcells; eauto.
      - iDestruct (sqex_support_intro with "Hthread") as (r) "[Hr Hsupport]".
        iExists r. iFrame. by iPureIntro. }
    iDestruct (sqex_support_big_sepM_with with "Hthreads") as (R) "(HR & #Hsupports & %Hfixed)".
    iDestruct (big_sepM2_dom with "Hsupports") as %Hdom.
    iDestruct (sqex_threads_reconstruct_resources _ _ _ _ _ Hnames Hrel
      with "Hstate HR Hsupports") as "(%Hcoherent & Hstate & Hthreads)".
    iExists (sqex_rebuild_threads C R). iFrame. iPureIntro.
    split; first by apply sqex_rebuild_threads_shapes. split; first done.
    intros i Hi. rewrite /sqex_rebuild_threads map_lookup_zip_with.
    destruct (C !! i) as [c|] eqn:Hc; rewrite Hc /=; last done.
    have Hr : is_Some (R !! i).
    { apply elem_of_dom. rewrite -Hdom.
      exact (elem_of_dom_2 (M := gmap nat) C i c Hc). }
    destruct Hr as [r Hr]. rewrite Hr /= -(Hfixed _ _ _ Hc Hr Hi).
    by destruct c.
  Qed.

  Lemma sqex_exact_thread_init m p hF e Φ :
    sq_heap_name ≠ sq_freeable_name ->
    uPred_ownM (sqex_state_resource m p hF) -∗
    own sq_heap_name (◯ sq_heap_cells m p) -∗ EXWP e {{ v, Φ v }} -∗
    uPred_ownM (sqex_state_resource m p hF) ∗
    sqex_exact_thread_inv m hF (SqexThread e p Φ).
  Proof.
    intros Hnames. iIntros "Hstate Hfrag Hwp".
    iDestruct (sqex_support_intro with "Hwp") as (r) "[Hr #Hsupport]".
    set (f := own.iRes_singleton sq_heap_name (◯ sq_heap_cells m p)).
    iAssert (uPred_ownM (r ⋅ f)) with "[Hr Hfrag]" as "Hr".
    { rewrite uPred.ownM_op. iFrame "Hr". by rewrite /f own.own_eq. }
    iDestruct (sqex_resource_fits_intro with "Hstate Hr") as "#Hfits".
    iDestruct (sqex_state_projection _ _ _ _ Hnames with "Hfits")
      as "[%Hproject _]".
    destruct Hproject as (_ & _ & Hinc).
    have Hfrag : sqex_heap_fragment (r ⋅ f) ≡ sq_heap_cells m p.
    { rewrite sqex_heap_fragment_op /f /sqex_heap_fragment
        sqex_project_singleton /sqex_auth_fragment /= in Hinc |- *.
      have Hr0 := sqex_heap_fragment_absorb _ _ Hinc.
      rewrite Hr0. change ((ε : sq_heapUR) ⋅ sq_heap_cells m p ≡ sq_heap_cells m p).
      by rewrite left_id. }
    iFrame "Hstate". iExists (r ⋅ f). iFrame "Hr Hfits". simpl. iSplit.
    - rewrite /sqex_support uPred.ownM_op.
      iIntros "!> [Hr _]". by iApply ("Hsupport" with "Hr").
    - iPureIntro. by symmetry.
  Qed.
End exact_threads.
