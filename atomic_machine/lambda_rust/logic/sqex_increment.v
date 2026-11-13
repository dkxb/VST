(** Two threads increment a shared cell with CAS. The parent waits until it
    observes both increments. Adequacy proves safety and that the parent
    returns 2 if it terminates. *)
From lrust.lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_rules.

Set Default Proof Using "Type".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

Definition sc_increment_loop : expr :=
  (rec: "inc" ["l"] :=
    let: "n" := !ˢᶜ "l" in
    if: CAS "l" "n" ("n" + #1)
    then #☠ else "inc" ["l"])%E.

Definition sc_increment (p : expr) : expr := sc_increment_loop [p].

Definition wait_for_two_loop : expr :=
  (rec: "wait" ["l"] :=
    let: "n" := !ˢᶜ "l" in
    if: "n" = #2 then "n" else "wait" ["l"])%E.

Definition wait_for_two (p : expr) : expr := wait_for_two_loop [p].

Definition two_increments : sq_expr :=
  (let: "l" := Alloc #1 in
   "l" <-ˢᶜ #0 ;;
   Fork (sc_increment "l") ;;
   sc_increment "l" ;;
   wait_for_two "l")%E.

Definition counterN : namespace := nroot .@ "sqex_counter".

Section proof.
  Context `{!lrSqGS Σ}.

  Definition counter_inv (l : loc) : iProp Σ :=
    ∃ n : Z, ⌜0 ≤ n⌝ ∗ l ↦ #n.

  Lemma sc_increment_spec l Φ :
    inv counterN (counter_inv l) -∗ ▷ Φ #☠ -∗
    EXWP sc_increment #l {{ Φ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /sc_increment. iLöb as "IH".
    iIntros "HΦ". rewrite /sc_increment_loop. exwp_pure (App _ _).
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
    exwp_bind (CAS _ _ _).
    iApply (exwp_cas_atomic _ (⊤ ∖ ↑counterN) _ (LitInt n) (LitInt (n + 1))).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n') "[>%Hn' Hl]".
    destruct (decide (n' = n)) as [->|Hneq].
    - iModIntro. iApply (conc_wp_cas_int_suc with "Hl").
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists (n + 1). iFrame. iPureIntro. lia. }
      iModIntro. exwp_pure (Case _ _).
      by iApply (exwp_value _ (LitV LitPoison)).
    - iModIntro. iApply (conc_wp_cas_int_fail with "Hl"); first congruence.
      iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists n'. iFrame. done. }
      iModIntro. exwp_pure (Case _ _). iApply "IH". by iNext.
  Qed.

  Lemma wait_for_two_spec l :
    inv counterN (counter_inv l) -∗
    EXWP wait_for_two #l {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    iIntros "#Hinv". rewrite /wait_for_two. iLöb as "IH".
    rewrite /wait_for_two_loop. exwp_pure (App _ _).
    exwp_bind (Read _ _).
    iApply (exwp_read_sc_atomic _ (⊤ ∖ ↑counterN)).
    iMod (inv_acc with "Hinv") as "[Hcounter Hclose]"; first set_solver.
    iDestruct "Hcounter" as (n) "[>%Hn Hl]".
    iModIntro. iApply (conc_wp_read_sc with "Hl").
    iNext. iIntros "Hl". iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists n. by iFrame. }
    iModIntro. exwp_pure (App _ _). exwp_pure (BinOp _ _ _).
    case_bool_decide as Hn2; exwp_pure (Case _ _).
    - iApply (exwp_value _ (LitV (LitInt n))). iPureIntro. by subst n.
    - iApply "IH".
  Qed.

  Lemma two_increments_spec :
    ⊢ EXWP two_increments {{ v, ⌜v = #2⌝ }}.
  Proof using All.
    rewrite /two_increments /sc_increment /wait_for_two
      /sc_increment_loop /wait_for_two_loop.
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
    exwp_bind (App sc_increment_loop _).
    iApply (sc_increment_spec with "Hinv"). iNext.
    exwp_pure (App _ _). by iApply wait_for_two_spec.
  Qed.
End proof.

Corollary two_increments_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [two_increments] [(fun v => v = #2)] m.
Proof.
  apply (sqex_adequacy Σ). intros. apply two_increments_spec.
Qed.
