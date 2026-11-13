(** Two threads share an invariant-protected cell and each increments it using
    an SC read followed by an SC write. The read/write pair is not atomic:
    the proof establishes safety and preserves a nonnegative counter, allowing
    a lost update. *)
From lrust.lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_rules.

Set Default Proof Using "Type".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

Definition sc_increment (p : expr) : expr :=
  (let: "n" := !ˢᶜ p in p <-ˢᶜ ("n" + #1))%E.

Definition two_increments : sq_expr :=
  (let: "l" := Alloc #1 in
   "l" <-ˢᶜ #0 ;;
   Fork (sc_increment "l") ;;
   sc_increment "l")%E.

Definition counterN : namespace := nroot .@ "sqex_counter".

Section proof.
  Context `{!lrSqGS Σ}.

  Definition counter_inv (l : loc) : iProp Σ :=
    ∃ n : Z, ⌜0 ≤ n⌝ ∗ l ↦ #n.

  Lemma sc_increment_spec l Φ :
    inv counterN (counter_inv l) -∗ ▷ Φ #☠ -∗
    EXWP sc_increment #l {{ Φ }}.
  Proof using All.
    iIntros "#Hinv HΦ". rewrite /sc_increment.
    exwp_bind (Read _ _).
    iApply (exwp_read_sc_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (conc_wp_read_sc with "Hl").
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro.
    exwp_pure (App _ _).
    exwp_pure (BinOp _ _ _).
    iApply (exwp_write_sc_atomic _ (⊤ ∖ ↑counterN) _ #(n + 1)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n') "[_ Hl]".
    iModIntro. iApply (conc_wp_write_sc with "Hl").
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists (n + 1). iFrame. iPureIntro. lia. }
    by iModIntro.
  Qed.

  Lemma two_increments_spec :
    ⊢ EXWP two_increments {{ v, ⌜v = #☠⌝ }}.
  Proof using All.
    rewrite /two_increments /sc_increment.
    exwp_bind (Alloc _).
    iApply exwp_alloc. iNext. iIntros (l) "Hl".
    exwp_pure (App _ _).
    exwp_bind (Write _ _ _).
    iApply (exwp_write_sc_atomic _ ⊤ _ #0).
    iModIntro. iApply (conc_wp_write_sc with "[Hl]"); first by iNext.
    iNext. iIntros "Hl".
    (* Initialization is an external call, so its postcondition can allocate
       the invariant before the following ordinary computation and fork. *)
    iMod (inv_alloc counterN _ (counter_inv l) with "[Hl]") as "#Hinv".
    { iNext. iExists 0. iFrame. done. }
    iModIntro. exwp_pure (App _ _).
    exwp_bind (Fork _).
    iApply (conc_wp_fork with "[]").
    { iNext. iApply (sc_increment_spec with "Hinv"). done. }
    iNext. iIntros "_". exwp_pure (App _ _).
    iApply (sc_increment_spec with "Hinv"). done.
  Qed.
End proof.

Corollary two_increments_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [two_increments] [(fun v => v = #☠)] m.
Proof.
  apply (sqex_adequacy Σ). intros. apply two_increments_spec.
Qed.
