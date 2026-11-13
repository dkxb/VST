(** Resource witnesses for the ownership carried by individual EXWP threads.
    The heap authority is shared. A thread's permission map bounds its own
    resource witness, rather than merely labelling its WP. *)
Require Export VST.atomic_machine.lambda_rust.logic.sq_heap.
From iris.algebra Require Import auth.
From iris.base_logic Require Import bi derived.

Set Default Proof Using "Type".

Section resource_witnesses.
  Context {Σ : gFunctors}.

  (** The plain wand records that [r] supports [P], at the current step index.
      Unlike a pure Coq entailment, this also represents later assertions. *)
  Definition sqex_support (P : iProp Σ) (r : iResUR Σ) : iProp Σ :=
    ■ (uPred_ownM r -∗ P).

  Lemma sqex_support_elim P r :
    uPred_ownM r -∗ sqex_support P r -∗ P.
  Proof. iIntros "Hr Hsupport". iApply ("Hsupport" with "Hr"). Qed.

  Lemma sqex_support_intro (P : iProp Σ) :
    P ⊢ ∃ r : iResUR Σ, uPred_ownM r ∗ sqex_support P r.
  Proof.
    rewrite /sqex_support /plainly.
    uPred.unseal. split=> n x Hvalid HP. cbn [uPred_holds].
    exists x, x, ε. split; first by rewrite right_id.
    split; first (change (x ≼{n} x); done).
    intros k y Hkn Hy Hown. change (uPred_holds P k (ε ⋅ y)). rewrite left_id.
    eapply uPred_mono; eauto.
  Qed.
  (** A plain consequence can be checked on a hypothetical compatible heap.
      This does not allocate or duplicate its authoritative resource. *)
  Lemma sqex_support_test (a r : iResUR Σ) P Q :
    (uPred_ownM a ∗ P ⊢ ■ Q) ->
    sqex_support P r ∧ ✓ (a ⋅ r) ⊢ ■ Q.
  Proof.
    intros [Htest]. revert Htest.
    rewrite /sqex_support /plainly /internal_cmra_valid.
    uPred.unseal. siProp_primitive.unseal.
    intros Htest. split=> n x Hvalid [Hsupport Hfit].
    change (✓{n} (a ⋅ r)) in Hfit.
    change (uPred_holds Q n ε).
    apply (Htest n (a ⋅ r)); first exact Hfit.
    exists a, r. split; first done.
    split; first (change (a ≼{n} a); done).
    specialize (Hsupport n r (Nat.le_refl n)).
    rewrite left_id in Hsupport.
    apply Hsupport.
    - exact (cmra_validN_op_r _ _ _ Hfit).
    - change (r ≼{n} r). done.
  Qed.
End resource_witnesses.

Section heap_support.
  Context `{!sq_heapGS Σ}.

  Definition sqex_heap_resource (m : lr_mem) (p : perm_map) : iResUR Σ :=
    own.iRes_singleton sq_heap_name (● sq_heap_cells m p).

  Definition sqex_state_resource (m : lr_mem) (p : perm_map)
      (hF : sq_freeableUR) : iResUR Σ :=
    sqex_heap_resource m p ⋅ own.iRes_singleton sq_freeable_name (● hF).

  (** This is a validity test with a hypothetical local authority, not
      ownership of another authority. It connects [p] to the actual resource
      supporting the thread's WP. *)
  Definition sqex_resource_fits (m : lr_mem) (p : perm_map) (hF : sq_freeableUR)
      (r : iResUR Σ) : iProp Σ := ✓ (sqex_state_resource m p hF ⋅ r).

  Lemma sqex_heap_resource_own m p :
    uPred_ownM (sqex_heap_resource m p) ⊣⊢
    own sq_heap_name (● sq_heap_cells m p).
  Proof. by rewrite own.own_eq. Qed.

  Lemma sqex_resource_fits_intro m p hF r :
    uPred_ownM (sqex_state_resource m p hF) -∗ uPred_ownM r -∗
    sqex_resource_fits m p hF r.
  Proof.
    rewrite /sqex_resource_fits.
    iIntros "Hheap Hr". iApply uPred.ownM_valid.
    by iApply (uPred.ownM_op with "[$Hheap $Hr]").
  Qed.

  Lemma sqex_state_resource_own m p hF :
    uPred_ownM (sqex_state_resource m p hF) ⊣⊢
      own sq_heap_name (● sq_heap_cells m p) ∗ own sq_freeable_name (● hF).
  Proof. by rewrite /sqex_state_resource uPred.ownM_op sqex_heap_resource_own own.own_eq. Qed.

  Lemma sqex_state_resource_heap m p hF :
    sq_heap_rel m p -> sq_freeable_rel m hF ->
    uPred_ownM (sqex_state_resource m p hF) ⊢ sq_heap_gen m p.
  Proof.
    intros Hrel HFrel. rewrite sqex_state_resource_own.
    iIntros "[Hm HF]". iExists hF. by iFrame.
  Qed.
End heap_support.
