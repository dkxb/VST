(** Heap resources shared by the sequential and atomic-machine logics.
    Each cell agrees on a value and a write version. A fraction q contributes
    q times that version to the explicit counter assertion below. Contributions
    add when fractions combine; their normalized versions must agree.
    [sq_heap_gen] fixes the per-location versions supplied by EXWP. Each
    step's events force the next versions, without retaining a history.
    [sq_heap] hides the versions for the reservation-based atomic logic. *)

From Stdlib Require Import Qcanon.
From iris.algebra Require Import auth gmap frac excl.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.
From iris.proofmode Require Export proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.

Set Default Proof Using "Type".

Definition sq_freeableUR : ucmra :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitO))).

Class sq_heapGS Σ := SqHeapGS {
  sq_heap_inG :: ghost_mapG Σ loc (val * nat);
  sq_freeable_inG :: inG Σ (authR sq_freeableUR);
  sq_heap_name : gname;
  sq_freeable_name : gname
}.

Fixpoint sq_inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
  match n with O => ∅ | S n => <[i0 := Excl ()]>(sq_inter (i0+1) n) end.

Definition sq_freeable_rel (m : lr_mem) (hF : sq_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs ->
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (m !! (blk, i)) ↔ is_Some (qs.2 !! i).

Definition sq_heap_cells (m : lr_mem) (ver_map : loc -> nat) : gmap loc (val * nat) :=
  map_imap (fun l v => Some (v, ver_map l)) m.

Lemma sq_heap_cells_lookup m ver_map l :
  sq_heap_cells m ver_map !! l = (fun v => (v, ver_map l)) <$> (m !! l).
Proof. unfold lr_mem in *. rewrite /sq_heap_cells map_lookup_imap. by destruct (m !! l). Qed.

Lemma sq_heap_cells_values m ver_map : fst <$> sq_heap_cells m ver_map = m.
Proof.
  unfold lr_mem in *. apply map_eq. intros l. rewrite lookup_fmap sq_heap_cells_lookup.
  unfold lr_mem in *. by destruct (m !! l).
Qed.

Lemma sq_heap_cells_insert m ver_map ver_map' l v :
  (forall k, k ≠ l -> ver_map' k = ver_map k) ->
  sq_heap_cells (<[l := v]> m) ver_map' = <[l := (v, ver_map' l)]> (sq_heap_cells m ver_map).
Proof.
  intros Hver_map. apply map_eq. intros k. rewrite sq_heap_cells_lookup.
  destruct (decide (k = l)) as [->|Hne].
  - by rewrite !lookup_insert_eq.
  - by rewrite !lookup_insert_ne // sq_heap_cells_lookup Hver_map.
Qed.

Lemma sq_heap_cells_delete m ver_map l :
  sq_heap_cells (delete l m) ver_map = delete l (sq_heap_cells m ver_map).
Proof.
  apply map_eq. intros k. rewrite sq_heap_cells_lookup.
  destruct (decide (k = l)) as [->|Hne].
  - by rewrite !lookup_delete_eq.
  - by rewrite !lookup_delete_ne // sq_heap_cells_lookup.
Qed.

Definition sq_count_next {A : Type} `{EqDecision A}
    (ver_map : A -> nat) (l : A) : A -> nat :=
  fun k => if decide (k = l) then S (ver_map k) else ver_map k.

(** Only the current step's events are inspected; no execution history is kept. *)
Definition sq_versions_after {A : Type} `{EqDecision A}
    (T : list (@mem_ev A)) (ver_map : A -> nat) : A -> nat :=
  foldl (fun ver_map ev => match ev with
    | atomic_machine.Write l => sq_count_next ver_map l
    | _ => ver_map
    end) ver_map T.

Definition sq_count_share (q : Qp) (n : nat) : Qc :=
  (Qp_to_Qc q * Qc_of_Z (Z.of_nat n))%Qc.

Lemma sq_count_share_add q1 q2 n :
  sq_count_share (q1 + q2) n = (sq_count_share q1 n + sq_count_share q2 n)%Qc.
Proof. by rewrite /sq_count_share Qp.to_Qc_inj_add Qcmult_plus_distr_l. Qed.

Section definitions.
  Context `{!sq_heapGS Σ}.

  Definition sq_pointsto (l : loc) (q : Qp) (v : val) : iProp Σ :=
    ∃ n : nat, l ↪[sq_heap_name]{#q} (v, n).

  (** The explicit contribution is rational: e.g. two halves at version 7
      each contribute 7/2. The ghost payload agrees on the normalized version,
      preventing a partial owner from incrementing just its contribution. *)
  Definition sq_pointsto_count (l : loc) (q : Qp) (v : val) (c : Qc) : iProp Σ :=
    ∃ n : nat, ⌜c = sq_count_share q n⌝ ∗ l ↪[sq_heap_name]{#q} (v, n).

  Definition sq_pointsto_vec (l : loc) (q : Qp) (vl : list val) : iProp Σ :=
    [∗ list] i ↦ v ∈ vl, sq_pointsto (l +ₗ i) q v.

  Definition sq_freeable (l : loc) (q : Qp) (n : nat) : iProp Σ :=
    own sq_freeable_name (◯ {[ l.1 := (q, sq_inter (l.2) n) ]}).

  Definition sq_heap_gen (m : lr_mem) (ver_map : loc -> nat) : iProp Σ :=
    ∃ hF, ghost_map_auth sq_heap_name 1 (sq_heap_cells m ver_map) ∗
      own sq_freeable_name (● hF) ∗ ⌜sq_freeable_rel m hF⌝.

  Definition sq_heap (m : lr_mem) : iProp Σ := ∃ ver_map, sq_heap_gen m ver_map.

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

Local Lemma delete_sq_free (σ : lr_mem) l l' n :
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
    intros q1 q2. rewrite /sq_pointsto. iSplit.
    - iIntros "Hl". iDestruct "Hl" as (n) "[H1 H2]".
      iSplitL "H1"; iExists n; iAssumption.
    - iIntros "[H1 H2]". iDestruct "H1" as (n1) "H1".
      iDestruct "H2" as (n2) "H2".
      iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
      injection Heq as ->. iExists n2. iCombine "H1 H2" as "H". iExact "H".
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

  Lemma sq_pointsto_count_forget l q v :
    (∃ c : Qc, sq_pointsto_count l q v c) ⊣⊢ l ↦{q} v.
  Proof.
    iSplit.
    - iIntros "(%c & %n & _ & Hl)". by iExists n.
    - iIntros "(%n & Hl)". iExists (sq_count_share q n), n. by iFrame.
  Qed.

  Lemma sq_pointsto_count_combine l q1 q2 v c1 c2 :
    sq_pointsto_count l q1 v c1 -∗ sq_pointsto_count l q2 v c2 -∗
    sq_pointsto_count l (q1 + q2) v (c1 + c2)%Qc.
  Proof.
    iIntros "(%n1 & -> & H1) (%n2 & -> & H2)".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    injection Heq as ->. iExists n2. rewrite sq_count_share_add.
    iCombine "H1 H2" as "H". by iFrame.
  Qed.

  Lemma sq_pointsto_count_split l q1 q2 v c :
    sq_pointsto_count l (q1 + q2) v c -∗
    ∃ c1 c2 : Qc, ⌜c = (c1 + c2)%Qc⌝ ∗
      sq_pointsto_count l q1 v c1 ∗ sq_pointsto_count l q2 v c2.
  Proof.
    iIntros "(%n & -> & [H1 H2])".
    iExists (sq_count_share q1 n), (sq_count_share q2 n).
    rewrite sq_count_share_add. iSplit; first done.
    iSplitL "H1"; iExists n; by iFrame.
  Qed.

  Lemma sq_heap_cells_pointsto m ver_map :
    ([∗ map] l ↦ vn ∈ sq_heap_cells m ver_map, l ↪[sq_heap_name] vn) -∗
    [∗ map] l ↦ v ∈ m, l ↦ v.
  Proof.
    rewrite -{2}(sq_heap_cells_values m ver_map) big_sepM_fmap.
    iApply big_sepM_mono. iIntros (l [v n] _) "Hl". by iExists n.
  Qed.

  Lemma sq_heap_gen_read m ver_map l q v :
    sq_heap_gen m ver_map -∗ l ↦{q} v -∗ ⌜m !! l = Some v⌝.
  Proof.
    iIntros "(%hF & Hm & _) (%n & Hl)".
    iDestruct (ghost_map_lookup with "Hm Hl") as %Hl.
    rewrite sq_heap_cells_lookup in Hl.
    destruct (m !! l); inversion Hl. done.
  Qed.

  Lemma sq_heap_read m l q v : sq_heap m -∗ l ↦{q} v -∗ ⌜m !! l = Some v⌝.
  Proof. iIntros "(%ver_map & Hm) Hl". by iApply (sq_heap_gen_read with "Hm Hl"). Qed.

  Lemma sq_heap_gen_write m ver_map ver_map' l v v' :
    (forall k, k ≠ l -> ver_map' k = ver_map k) ->
    sq_heap_gen m ver_map -∗ l ↦ v ==∗ sq_heap_gen (<[l := v']> m) ver_map' ∗ l ↦ v'.
  Proof.
    iIntros (Hver_map) "(%hF & Hm & HF & %Hrel) (%n & Hl)".
    iDestruct (ghost_map_lookup with "Hm Hl") as %Hl.
    iMod (ghost_map_update (v', ver_map' l) with "Hm Hl") as "[Hm Hl]".
    iModIntro. iSplitL "Hm HF".
    - iExists hF. rewrite (sq_heap_cells_insert _ _ _ _ _ Hver_map). iFrame. iPureIntro.
      eapply sq_freeable_rel_stable; first done.
      rewrite sq_heap_cells_lookup in Hl. destruct (m !! l); naive_solver.
    - by iExists (ver_map' l).
  Qed.

  Lemma sq_heap_gen_version m ver_map l q v n :
    sq_heap_gen m ver_map -∗ l ↪[sq_heap_name]{#q} (v, n) -∗ ⌜n = ver_map l⌝.
  Proof.
    iIntros "(%hF & Hm & _) Hl".
    iDestruct (ghost_map_lookup with "Hm Hl") as %Hl.
    rewrite sq_heap_cells_lookup in Hl.
    destruct (m !! l); inversion Hl. done.
  Qed.

  (** Even a same-value write cannot advance its version with a fraction
      framed outside the update. [R] denotes any resources used by it. *)
  Lemma sq_heap_gen_write_frame m m' ver_map l q v (R : iProp Σ) :
    sq_heap_gen m ver_map -∗ l ↦{q} v -∗ R -∗
    ⌜¬ (sq_heap_gen m ver_map ∗ R ⊢ |==>
      sq_heap_gen m' (sq_versions_after [lr_write_event l] ver_map))⌝.
  Proof.
    iIntros "Hm (%n & Hl) HR" (Hupdate).
    iDestruct (sq_heap_gen_version with "Hm Hl") as %Hbefore.
    iApply (bupd_elim _).
    iMod (Hupdate with "[$Hm $HR]") as "Hm".
    iDestruct (sq_heap_gen_version with "Hm Hl") as %Hafter.
    rewrite /sq_versions_after /= /sq_count_next decide_True in Hafter; last done.
    lia.
  Qed.

  Lemma sq_heap_gen_write_step m ver_map l v v' :
    sq_heap_gen m ver_map -∗ l ↦ v ==∗
      sq_heap_gen (<[l := v']> m) (sq_versions_after [lr_write_event l] ver_map) ∗ l ↦ v'.
  Proof.
    apply sq_heap_gen_write. intros k Hne.
    by rewrite /sq_versions_after /= /sq_count_next decide_False.
  Qed.

  (** A full contribution increases by one when this write rule is used.
      This is an update law, not an inversion theorem for arbitrary WP proofs:
      [sq_heap] itself does not force a same-value write to invoke this law. *)
  Lemma sq_heap_write_count m l v v' c :
    sq_heap m -∗ sq_pointsto_count l 1 v c ==∗
      sq_heap (<[l := v']> m) ∗ sq_pointsto_count l 1 v' (c + 1)%Qc.
  Proof.
    iIntros "(%ver_map & %hF & Hm & HF & %Hrel) (%n & -> & Hl)".
    iDestruct (ghost_map_lookup with "Hm Hl") as %Hl.
    assert (m !! l = Some v /\ ver_map l = n) as [Hlookup Hn].
    { rewrite sq_heap_cells_lookup in Hl.
      destruct (m !! l); inversion Hl. done. }
    iMod (ghost_map_update (v', S n) with "Hm Hl") as "[Hm Hl]".
    iModIntro. iSplitL "Hm HF".
    - iExists (sq_count_next ver_map l), hF.
      rewrite (sq_heap_cells_insert _ ver_map (sq_count_next ver_map l)).
      2: { intros k Hne. by rewrite /sq_count_next decide_False. }
      rewrite /sq_count_next decide_True // Hn. iFrame. iPureIntro.
      eapply sq_freeable_rel_stable; [exact Hrel | by eexists].
    - iExists (S n). iFrame. iPureIntro.
      change (1 * Qc_of_Z (Z.of_nat n) + 1 =
        1 * Qc_of_Z (Z.of_nat (S n)))%Qc.
      rewrite !Qcmult_1_l Nat2Z.inj_succ -Z.add_1_r Z2Qc_inj_add Z2Qc_inj_1.
      done.
  Qed.

  Lemma sq_heap_write m l v v' :
    sq_heap m -∗ l ↦ v ==∗ sq_heap (<[l := v']> m) ∗ l ↦ v'.
  Proof.
    iIntros "Hm (%n & Hl)".
    iMod (sq_heap_write_count _ _ _ _ (sq_count_share 1 n) with "Hm [Hl]")
      as "[$ (%n' & _ & Hl)]".
    { iExists n. by iFrame. }
    iModIntro. by iExists n'.
  Qed.

  Local Lemma sq_heap_alloc_values m ver_map l n :
    (∀ z : Z, m !! (l +ₗ z) = None) ->
    ghost_map_auth sq_heap_name 1 (sq_heap_cells m ver_map) ==∗
      ghost_map_auth sq_heap_name 1 (sq_heap_cells (alloc_gmap (LitV LitPoison) l n m) ver_map) ∗
      l ↦∗ repeat (LitV LitPoison) n.
  Proof.
    revert l. induction n as [|n IH]=> l Hfresh.
    { iIntros "$ !>". by rewrite sq_pointsto_vec_nil. }
    iIntros "Hm".
    iMod (IH (l +ₗ 1) with "Hm") as "[Hm Hl]".
    { intros z. by rewrite shift_loc_assoc. }
    iMod (ghost_map_insert l (LitV LitPoison, ver_map l) with "Hm") as "[Hm Hv]".
    { rewrite sq_heap_cells_lookup lookup_sq_alloc_ne; last (simpl; lia). by rewrite -(shift_loc_0 l) Hfresh. }
    iModIntro. simpl. rewrite (sq_heap_cells_insert _ ver_map ver_map); last done.
    rewrite sq_pointsto_vec_cons. by iFrame.
  Qed.

  Lemma sq_heap_gen_alloc m ver_map l (n : Z) :
    0 < n -> (∀ z, m !! (l +ₗ z) = None) ->
    sq_heap_gen m ver_map ==∗ sq_heap_gen (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m) ver_map ∗
      †l…(Z.to_nat n) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    iIntros (Hn Hfresh) "(%hF & Hm & HF & %Hrel)".
    assert (Z.to_nat n ≠ O) by lia.
    iMod (sq_heap_alloc_values with "Hm") as "[Hm $]"; first done.
    iMod (own_update _ (● hF) with "HF") as "[HF Hfree]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, sq_inter (l.2) (Z.to_nat n))).
      - eauto using sq_freeable_rel_None.
      - split; first done. apply sq_inter_valid. }
    iModIntro. iFrame "Hfree". iExists _. iFrame. iPureIntro.
    by apply sq_freeable_rel_alloc.
  Qed.

  Local Lemma sq_heap_free_values m ver_map l vl :
    ghost_map_auth sq_heap_name 1 (sq_heap_cells m ver_map) -∗ l ↦∗ vl ==∗
      ghost_map_auth sq_heap_name 1 (sq_heap_cells (free_gmap l (length vl) m) ver_map).
  Proof.
    revert m l. induction vl as [|v vl IH]=> m l.
    { by iIntros "$ _". }
    rewrite sq_pointsto_vec_cons. iIntros "Hm [(%n & Hv) Hl]".
    iMod (ghost_map_delete with "Hm Hv") as "Hm".
    iEval (rewrite -sq_heap_cells_delete) in "Hm".
    iMod (IH with "Hm Hl") as "Hm".
    simpl. rewrite delete_sq_free. by iFrame.
  Qed.

  Lemma sq_heap_gen_free m ver_map l vl (n : Z) :
    n = length vl ->
    sq_heap_gen m ver_map -∗ l ↦∗ vl -∗ †l…(length vl) ==∗
      ⌜0 < n⌝ ∗ ⌜∀ z, is_Some (m !! (l +ₗ z)) ↔ 0 ≤ z < n⌝ ∗
      sq_heap_gen (free_gmap l (Z.to_nat n) m) ver_map.
  Proof.
    iIntros (Hn) "(%hF & Hm & HF & %Hrel) Hl Hfree".
    iCombine "HF Hfree" gives %[Hin Hvalid]%auth_both_valid_discrete.
    move: Hin=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hlookup Hin]].
    apply (Some_included_exclusive _ _) in Hin as [=<-<-]%leibniz_equiv; last first.
    { move: (Hvalid (l.1)). rewrite Hlookup. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (Hrel (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (sq_heap_free_values with "Hm Hl") as "Hm".
    iMod (own_update_2 with "HF Hfree") as "HF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst n. repeat iSplit; eauto using sq_freeable_is_Some.
    iExists _. rewrite Nat2Z.id. iFrame. iPureIntro.
    by eapply sq_freeable_rel_free.
  Qed.
  Lemma sq_heap_alloc m l (n : Z) :
    0 < n -> (∀ z, m !! (l +ₗ z) = None) ->
    sq_heap m ==∗ sq_heap (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m) ∗
      †l…(Z.to_nat n) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    iIntros (Hn Hfresh) "(%ver_map & Hm)".
    iMod (sq_heap_gen_alloc with "Hm") as "[Hm $]"; [done | done | ].
    iModIntro. by iExists ver_map.
  Qed.

  Lemma sq_heap_free m l vl (n : Z) :
    n = length vl ->
    sq_heap m -∗ l ↦∗ vl -∗ †l…(length vl) ==∗
      ⌜0 < n⌝ ∗ ⌜∀ z, is_Some (m !! (l +ₗ z)) ↔ 0 ≤ z < n⌝ ∗
      sq_heap (free_gmap l (Z.to_nat n) m).
  Proof.
    iIntros (Hn) "(%ver_map & Hm) Hl Hfree".
    iMod (sq_heap_gen_free _ _ _ _ n Hn with "Hm Hl Hfree") as "[$ [$ Hm]]".
    iModIntro. by iExists ver_map.
  Qed.
End heap.
