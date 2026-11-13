(** Heap resources shared by the sequential and atomic-machine logics.
    Values live in the physical memory; a separate permission map records
    the thread's total ownership at each location. Points-to assertions
    own fragments of that total, coupled with agreement on the value. *)

From iris.algebra Require Import auth gmap frac agree excl.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.
From iris.proofmode Require Export proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.

Set Default Proof Using "Type".

Definition sq_heapUR : ucmra := gmapUR loc (prodR fracR (agreeR (leibnizO val))).
Definition sq_freeableUR : ucmra :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitO))).

Class sq_heapGS Σ := SqHeapGS {
  sq_heap_inG :: inG Σ (authR sq_heapUR);
  sq_freeable_inG :: inG Σ (authR sq_freeableUR);
  sq_heap_name : gname;
  sq_freeable_name : gname
}.

Definition perm_map := gmap loc Qp.
Definition sq_heap_cells (m : lr_mem) (p : perm_map) : sq_heapUR :=
  map_zip_with (fun q v => (q, to_agree v)) p m.
Definition sq_full_heap (m : lr_mem) : perm_map := (fun _ => 1%Qp) <$> m.
(** Every owned location must be allocated: [dom p ⊆ dom m]. *)
Definition sq_heap_rel (m : lr_mem) (p : perm_map) : Prop :=
  (dom p : gset loc) ⊆ dom m.

Lemma sq_heap_cells_lookup m p l :
  sq_heap_cells m p !! l =
    (q ← p !! l; v ← m !! l; Some (q, to_agree v)).
Proof. by rewrite /sq_heap_cells map_lookup_zip_with. Qed.

Lemma sq_heap_cells_insert m p l v q :
  sq_heap_cells (<[l := v]> m) (<[l := q]> p) =
    <[l := (q, to_agree v)]> (sq_heap_cells m p).
Proof. by rewrite /sq_heap_cells map_insert_zip_with. Qed.

Lemma sq_heap_cells_write m p l v q :
  p !! l = Some q ->
  sq_heap_cells (<[l := v]> m) p =
    <[l := (q, to_agree v)]> (sq_heap_cells m p).
Proof.
  intros Hl. rewrite -sq_heap_cells_insert. by rewrite (insert_id p l q).
Qed.

Lemma sq_heap_cells_delete m p l :
  sq_heap_cells (delete l m) (delete l p) = delete l (sq_heap_cells m p).
Proof. by rewrite /sq_heap_cells map_delete_zip_with. Qed.

Lemma sq_heap_rel_insert m p l v q :
  sq_heap_rel m p -> sq_heap_rel (<[l := v]> m) (<[l := q]> p).
Proof.
  unfold sq_heap_rel, lr_mem, perm_map. rewrite !dom_insert_L. set_solver.
Qed.

Lemma sq_heap_rel_delete m p l :
  sq_heap_rel m p -> sq_heap_rel (delete l m) (delete l p).
Proof.
  unfold sq_heap_rel, lr_mem, perm_map. rewrite !dom_delete_L. set_solver.
Qed.

Lemma sq_heap_cells_valid m p :
  (forall l q, p !! l = Some q -> (q ≤ 1)%Qp) -> ✓ sq_heap_cells m p.
Proof.
  intros Hq l. rewrite sq_heap_cells_lookup.
  destruct (p !! l) as [q|] eqn:Hl; simpl; last done.
  destruct (m !! l) as [v|]; simpl; last done.
  split; [by eapply Hq | done].
Qed.

Lemma sq_full_heap_valid m : ✓ sq_heap_cells m (sq_full_heap m).
Proof.
  unfold lr_mem in *. apply sq_heap_cells_valid. intros l q.
  rewrite /sq_full_heap lookup_fmap. destruct (m !! l); simpl; intros Heq; inversion Heq; subst; done.
Qed.

Lemma sq_full_heap_rel m : sq_heap_rel m (sq_full_heap m).
Proof.
  unfold sq_heap_rel, sq_full_heap, lr_mem, perm_map. by rewrite dom_fmap_L.
Qed.

Fixpoint sq_inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
  match n with O => ∅ | S n => <[i0 := Excl ()]>(sq_inter (i0+1) n) end.

Definition sq_freeable_rel (m : lr_mem) (hF : sq_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs ->
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (m !! (blk, i)) ↔ is_Some (qs.2 !! i).

(** Sequential events cannot transfer ownership between threads. Values may
    change on writes, but the permission map stays unchanged and ownership
    must be full, even for same-value writes. External calls do not use this
    relation. *)
Section permissions.
  Context {Loc : Type} `{Countable Loc}.
  Local Notation heap := (gmap Loc Qp).

  Inductive perm_event : @mem_ev Loc -> heap -> heap -> Prop :=
  | PermRead h l q : h !! l = Some q ->
      perm_event (atomic_machine.Read l) h h
  | PermWrite h l : h !! l = Some 1%Qp ->
      perm_event (atomic_machine.Write l) h h
  | PermAlloc h l : h !! l = None ->
      perm_event (atomic_machine.Alloc l) h (<[l := 1%Qp]> h)
  | PermFree h l : h !! l = Some 1%Qp ->
      perm_event (atomic_machine.Free l) h (delete l h).

  Inductive perm_step : list (@mem_ev Loc) -> heap -> heap -> Prop :=
  | PermNil h : perm_step [] h h
  | PermCons ev T h1 h2 h3 : perm_event ev h1 h2 ->
      perm_step T h2 h3 -> perm_step (ev :: T) h1 h3.

  Lemma perm_step_singleton ev h1 h2 :
    perm_step [ev] h1 h2 <-> perm_event ev h1 h2.
  Proof.
    split.
    - inversion 1; subst.
      match goal with Hnil : perm_step [] _ _ |- _ => inversion Hnil; subst; done end.
    - intro. econstructor; eauto using PermNil.
  Qed.
End permissions.

Section definitions.
  Context `{!sq_heapGS Σ}.

  Definition sq_pointsto (l : loc) (q : Qp) (v : val) : iProp Σ :=
    own sq_heap_name (◯ {[l := (q, to_agree v)]}).
  Definition sq_pointsto_vec (l : loc) (q : Qp) (vl : list val) : iProp Σ :=
    [∗ list] i ↦ v ∈ vl, sq_pointsto (l +ₗ i) q v.
  Definition sq_freeable (l : loc) (q : Qp) (n : nat) : iProp Σ :=
    own sq_freeable_name (◯ {[ l.1 := (q, sq_inter (l.2) n) ]}).

  Definition sq_heap_gen (m : lr_mem) (h : perm_map) : iProp Σ :=
    ∃ hF, own sq_heap_name (● sq_heap_cells m h) ∗
      own sq_freeable_name (● hF) ∗ ⌜sq_heap_rel m h ∧ sq_freeable_rel m hF⌝.
  Definition sq_heap (m : lr_mem) : iProp Σ := ∃ h, sq_heap_gen m h.
End definitions.

Notation "l ↦{ q } v" := (sq_pointsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (sq_pointsto l 1 v) (at level 20) : bi_scope.
Notation "l ↦∗{ q } vl" := (sq_pointsto_vec l q vl)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
Notation "l ↦∗ vl" := (sq_pointsto_vec l 1 vl) (at level 20) : bi_scope.
Notation "†{ q } l … n" := (sq_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (sq_freeable l 1 n) (at level 20) : bi_scope.

Local Lemma lookup_sq_alloc (σ : lr_mem) (l l' : loc) (n : nat) :
  l.1 = l'.1 → l.2 ≤ l'.2 < l.2 + n →
  alloc_gmap (LitV LitPoison) l n σ !! l' = Some (LitV LitPoison).
Proof.
  intros ?. destruct l' as [? l']; simplify_eq/=.
  revert l. induction n as [|n IH]=> /= l Hl; [lia|].
  assert (l' = l.2 ∨ l.2 + 1 ≤ l') as [->|?] by lia.
  { by rewrite -surjective_pairing lookup_insert_eq. }
  rewrite lookup_insert_ne; last by destruct l; intros ?; simplify_eq/=; lia.
  rewrite -(shift_loc_block l 1) IH /=; last lia. done.
Qed.

Local Lemma lookup_sq_alloc_ne (σ : lr_mem) (l l' : loc) (n : nat) :
  l.1 ≠ l'.1 ∨ l'.2 < l.2 ∨ l.2 + n ≤ l'.2 →
  alloc_gmap (LitV LitPoison) l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> /= l Hl; auto.
  rewrite -(IH (l +ₗ 1)); last (simpl; intuition lia).
  apply lookup_insert_ne. intros ->; intuition lia.
Qed.

Local Lemma lookup_sq_free_ne (σ : lr_mem) l l' n : l.1 ≠ l'.1 → free_gmap l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> l ? //=.
  rewrite lookup_delete_ne; last congruence.
  apply IH. by rewrite shift_loc_block.
Qed.

Local Lemma delete_sq_free {A : Type} (σ : gmap loc A) l l' n :
  delete l (free_gmap l' n σ) = free_gmap l' n (delete l σ).
Proof.
  revert l'. induction n as [|n IH]=> l' //=. by rewrite delete_delete IH.
Qed.

Section freeable.
  Implicit Types σ : lr_mem.

  Lemma sq_inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → sq_inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma sq_inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → sq_inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma sq_inter_valid i n : ✓ sq_inter i n.
  Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

  Lemma sq_freeable_rel_None σ l hF :
    (∀ m : Z, σ !! (l +ₗ m) = None) → sq_freeable_rel σ hF →
    hF !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH (i - l.2)). by rewrite /shift_loc Zplus_minus.
  Qed.

  Lemma sq_freeable_is_Some σ hF l n i :
    sq_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, sq_inter (l.2) n) →
    is_Some (σ !! (l +ₗ i)) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /shift_loc /=. intros REL Hl.
    destruct (REL b (1%Qp, sq_inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt sq_inter_lookup_Some; lia.
    - rewrite is_Some_alt sq_inter_lookup_None; lia.
  Qed.

  Lemma sq_freeable_rel_alloc l h n σ:
    n ≠ O →
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    sq_freeable_rel σ h →
    sq_freeable_rel (alloc_gmap (LitV LitPoison) l n σ)
                      (<[l.1 := (1%Qp, sq_inter (l.2) n)]> h).
  Proof.
    move=> Hvlnil FRESH REL blk qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct n as [|n]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (l.2 ≤ i ∧ i < l.2 + n)).
      + rewrite sq_inter_lookup_Some // lookup_sq_alloc; naive_solver.
      + rewrite sq_inter_lookup_None; last lia. rewrite lookup_sq_alloc_ne /=; last lia.
        replace (l.1,i) with (l +ₗ (i - l.2)) by (rewrite /shift_loc; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL blk qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_sq_alloc_ne; last auto.
  Qed.

  Lemma sq_freeable_rel_free σ hF n l :
    hF !! l.1 = Some (1%Qp, sq_inter (l.2) n) →
    sq_freeable_rel σ hF →
    sq_freeable_rel (free_gmap l n σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_sq_free_ne.
  Qed.

  Lemma sq_freeable_rel_stable σ h l p :
    sq_freeable_rel σ h → is_Some (σ !! l) →
    sq_freeable_rel (<[l := p]>σ) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.

End freeable.

Section heap.
  Context `{!sq_heapGS Σ}.
  Implicit Types m : lr_mem.

  Global Instance sq_pointsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. apply _. Qed.
  Global Instance sq_pointsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros q1 q2. rewrite /sq_pointsto -own_op -auth_frag_op singleton_op.
    by rewrite -pair_op /= agree_idemp.
  Qed.
  Global Instance sq_pointsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split; first done. apply _. Qed.
  Global Instance sq_pointsto_vec_timeless l q vl : Timeless (l ↦∗{q} vl).
  Proof. apply _. Qed.
  Global Instance sq_freeable_timeless l q n : Timeless (†{q}l…n).
  Proof. apply _. Qed.

  Lemma sq_pointsto_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /sq_pointsto_vec. Qed.
  Lemma sq_pointsto_vec_cons l q v vl :
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vl.
  Proof.
    rewrite /sq_pointsto_vec big_sepL_cons shift_loc_0.
    f_equiv. apply big_sepL_proper. intros k w _.
    by rewrite shift_loc_assoc Nat2Z.inj_succ Z.add_1_l.
  Qed.

  Lemma sq_pointsto_valid_2 l q1 q2 v1 v2 :
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ v1 = v2⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
    move: Hv. rewrite -auth_frag_op singleton_op auth_frag_valid
      singleton_valid -pair_op pair_valid /= to_agree_op_valid_L. done.
  Qed.

  (** A points-to fraction is bounded by the total stored at its location. *)
  Lemma sq_heap_gen_lookup m p l q v :
    sq_heap_gen m p -∗ l ↦{q} v -∗
    ⌜m !! l = Some v ∧ exists qt, p !! l = Some qt ∧ (q ≤ qt ≤ 1)%Qp⌝.
  Proof.
    unfold perm_map in *. iIntros "(%hF & Hh & _) Hl".
    iCombine "Hh Hl" gives %[Hin Hvalid]%auth_both_valid_discrete.
    move: Hin=> /singleton_included_l [x [Hx Hin]].
    rewrite sq_heap_cells_lookup in Hx.
    destruct (p !! l) as [qt|] eqn:Hp; rewrite Hp /= in Hx; last by inversion Hx.
    destruct (m !! l) as [w|] eqn:Hm; rewrite /= in Hx; last by inversion Hx.
    rewrite -Hx in Hin.
    have Hqt : (qt ≤ 1)%Qp.
    { specialize (Hvalid l). rewrite sq_heap_cells_lookup Hp Hm in Hvalid.
      exact (proj1 Hvalid). }
    iPureIntro. move: Hin=> /Some_included [Heq | Hin].
    - destruct Heq as [Hq Hv]. apply (inj to_agree) in Hv.
      change (q = qt) in Hq. change (v = w) in Hv. subst. eauto.
    - move: Hin=> /pair_included [Hq Hv].
      apply to_agree_included in Hv. change (v = w) in Hv. subst.
      split; first done. exists qt. split; first done.
      split; [by apply frac_included_weak | done].
  Qed.

  Lemma sq_heap_gen_read m p l q v :
    sq_heap_gen m p -∗ l ↦{q} v -∗ ⌜m !! l = Some v⌝.
  Proof.
    iIntros "Hm Hl". iDestruct (sq_heap_gen_lookup with "Hm Hl") as %[Hread _]. done.
  Qed.

  Lemma sq_heap_gen_missing m p l :
    m !! l = None -> sq_heap_gen m p -∗ ⌜p !! l = None⌝.
  Proof.
    iIntros (Hnone) "(%hF & _ & _ & [%Hrel _])". iPureIntro.
    apply (not_elem_of_dom (D := gset loc)).
    apply (not_elem_of_dom (D := gset loc)) in Hnone.
    unfold sq_heap_rel in Hrel. set_solver.
  Qed.

  Lemma sq_heap_gen_full m p l v :
    sq_heap_gen m p -∗ l ↦ v -∗ ⌜p !! l = Some 1%Qp⌝.
  Proof.
    iIntros "Hm Hl". iDestruct (sq_heap_gen_lookup with "Hm Hl") as %(_ & q & Hp & Hlo & Hhi).
    have Hq : q = 1%Qp by apply (anti_symm (≤)%Qp). subst q. done.
  Qed.

  Lemma sq_heap_read m l q v : sq_heap m -∗ l ↦{q} v -∗ ⌜m !! l = Some v⌝.
  Proof. iIntros "(%h & Hm) Hl". by iApply (sq_heap_gen_read with "Hm Hl"). Qed.

  Lemma sq_heap_gen_write m p l v v' :
    sq_heap_gen m p -∗ l ↦ v ==∗
    sq_heap_gen (<[l := v']> m) p ∗ l ↦ v'.
  Proof.
    iIntros "Hm Hl". iDestruct (sq_heap_gen_full with "Hm Hl") as %Hp.
    iDestruct (sq_heap_gen_read with "Hm Hl") as %Hm.
    iDestruct "Hm" as (hF) "(Hm & HF & [%Hrel %HFrel])".
    iMod (own_update_2 with "Hm Hl") as "[Hm Hl]".
    { apply auth_update, (singleton_local_update _ _ (1%Qp, to_agree v)).
      - by rewrite sq_heap_cells_lookup Hp Hm.
      - apply (exclusive_local_update _ (1%Qp, to_agree v')). done. }
    iModIntro. iFrame "Hl". iExists hF.
    rewrite (sq_heap_cells_write _ _ _ _ _ Hp). iFrame. iPureIntro. split.
    - unfold sq_heap_rel in *. rewrite dom_insert_L. set_solver.
    - eapply sq_freeable_rel_stable; first done. by exists v.
  Qed.

  Lemma sq_heap_write m l v v' :
    sq_heap m -∗ l ↦ v ==∗ sq_heap (<[l := v']> m) ∗ l ↦ v'.
  Proof.
    iIntros "(%h & Hm) Hl". iMod (sq_heap_gen_write with "Hm Hl") as "[Hm $]".
    iModIntro. by iExists _.
  Qed.

  Local Lemma sq_heap_alloc_values m p l n :
    (∀ z : Z, m !! (l +ₗ z) = None) -> sq_heap_rel m p ->
    own sq_heap_name (● sq_heap_cells m p) ==∗
    own sq_heap_name (● sq_heap_cells (alloc_gmap (LitV LitPoison) l n m)
      (alloc_gmap 1%Qp l n p)) ∗
    ⌜sq_heap_rel (alloc_gmap (LitV LitPoison) l n m)
      (alloc_gmap 1%Qp l n p)⌝ ∗
    l ↦∗ repeat (LitV LitPoison) n.
  Proof.
    revert m p l. induction n as [|n IH]=> m p l Hfresh Hrel.
    { iIntros "$ !>". rewrite sq_pointsto_vec_nil. auto. }
    iIntros "Hp".
    iMod (IH m p (l +ₗ 1) with "Hp") as "(Hp & %Hrel' & Hl)".
    { intros z. by rewrite shift_loc_assoc. }
    { exact Hrel. }
    have Hnone : alloc_gmap (LitV LitPoison) (l +ₗ 1) n m !! l = None.
    { rewrite lookup_sq_alloc_ne; last (simpl; lia).
      by rewrite -(shift_loc_0 l) Hfresh. }
    iMod (own_update with "Hp") as "[Hp Hv]".
    { apply auth_update_alloc, (alloc_singleton_local_update _ l (1%Qp, to_agree (LitV LitPoison))).
      - rewrite sq_heap_cells_lookup Hnone.
        by destruct (alloc_gmap 1%Qp (l +ₗ 1) n p !! l) eqn:Hp; rewrite Hp.
      - done. }
    iModIntro. simpl. rewrite sq_heap_cells_insert sq_pointsto_vec_cons.
    iFrame. iPureIntro. by apply sq_heap_rel_insert.
  Qed.

  Lemma sq_heap_gen_alloc m h l (n : Z) :
    0 < n -> (∀ z, m !! (l +ₗ z) = None) ->
    sq_heap_gen m h ==∗
    sq_heap_gen (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m)
      (alloc_gmap 1%Qp l (Z.to_nat n) h) ∗
    †l…(Z.to_nat n) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    iIntros (Hn Hfresh) "(%hF & Hm & HF & [%Hrel %HFrel])".
    assert (Z.to_nat n ≠ O) by lia.
    iMod (sq_heap_alloc_values with "Hm") as "(Hm & %Hrel' & $)"; [done | done | ].
    iMod (own_update _ (● hF) with "HF") as "[HF Hfree]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, sq_inter (l.2) (Z.to_nat n))).
      - eauto using sq_freeable_rel_None.
      - split; first done. apply sq_inter_valid. }
    iModIntro. iFrame "Hfree". iExists _. iFrame. iPureIntro.
    split; first done. by apply sq_freeable_rel_alloc.
  Qed.

  Local Lemma sq_heap_free_values m p l vl :
    sq_heap_rel m p ->
    own sq_heap_name (● sq_heap_cells m p) -∗ l ↦∗ vl ==∗
    own sq_heap_name (● sq_heap_cells (free_gmap l (length vl) m)
      (free_gmap l (length vl) p)) ∗
    ⌜sq_heap_rel (free_gmap l (length vl) m) (free_gmap l (length vl) p)⌝.
  Proof.
    revert m p l. induction vl as [|v vl IH]=> m p l Hrel.
    { iIntros "$ _ !>". done. }
    rewrite sq_pointsto_vec_cons. iIntros "Hm [Hv Hl]".
    iMod (own_update_2 with "Hm Hv") as "Hm".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iEval (rewrite -sq_heap_cells_delete) in "Hm".
    iMod (IH (delete l m) (delete l p) with "Hm Hl") as "[Hm %Hrel']".
    { by apply sq_heap_rel_delete. }
    simpl. rewrite !delete_sq_free. by iFrame.
  Qed.

  Lemma sq_heap_gen_free m h l vl (n : Z) :
    n = length vl ->
    sq_heap_gen m h -∗ l ↦∗ vl -∗ †l…(length vl) ==∗
      ⌜0 < n⌝ ∗ ⌜∀ z, is_Some (m !! (l +ₗ z)) ↔ 0 ≤ z < n⌝ ∗
      sq_heap_gen (free_gmap l (Z.to_nat n) m) (free_gmap l (Z.to_nat n) h).
  Proof.
    iIntros (Hn) "(%hF & Hm & HF & [%Hrel %HFrel]) Hl Hfree".
    iCombine "HF Hfree" gives %[Hin Hvalid]%auth_both_valid_discrete.
    move: Hin=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hlookup Hin]].
    apply (Some_included_exclusive _ _) in Hin as [=<-<-]%leibniz_equiv; last first.
    { move: (Hvalid (l.1)). rewrite Hlookup. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (HFrel (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (sq_heap_free_values with "Hm Hl") as "[Hm %Hrel']"; first done.
    iMod (own_update_2 with "HF Hfree") as "HF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst n. repeat iSplit; eauto using sq_freeable_is_Some.
    iExists _. rewrite Nat2Z.id. iFrame. iPureIntro.
    split; first done. by eapply sq_freeable_rel_free.
  Qed.

  Lemma sq_heap_alloc m l (n : Z) :
    0 < n -> (∀ z, m !! (l +ₗ z) = None) ->
    sq_heap m ==∗ sq_heap (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m) ∗
      †l…(Z.to_nat n) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    iIntros (Hn Hfresh) "(%h & Hm)".
    iMod (sq_heap_gen_alloc with "Hm") as "[Hm $]"; [done | done | ].
    iModIntro. by iExists _.
  Qed.

  Lemma sq_heap_free m l vl (n : Z) :
    n = length vl ->
    sq_heap m -∗ l ↦∗ vl -∗ †l…(length vl) ==∗
      ⌜0 < n⌝ ∗ ⌜∀ z, is_Some (m !! (l +ₗ z)) ↔ 0 ≤ z < n⌝ ∗
      sq_heap (free_gmap l (Z.to_nat n) m).
  Proof.
    iIntros (Hn) "(%h & Hm) Hl Hfree".
    iMod (sq_heap_gen_free _ _ _ _ n Hn with "Hm Hl Hfree") as "[$ [$ Hm]]".
    iModIntro. by iExists _.
  Qed.
End heap.
