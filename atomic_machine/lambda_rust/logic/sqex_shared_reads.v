(** Two fractional owners perform non-atomic reads in separate threads.
    Both reads may be between Try and Commit simultaneously. *)
From lrust.lang Require Import notation.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_rules.

Set Default Proof Using "Type".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

Definition shared_reads : sq_expr :=
  (let: "l" := Alloc #1 in
   "l" <- #7 ;;
   Fork (! "l") ;;
   ! "l")%E.

Section shared_reads_proof.
  Context `{!lrSqGS Σ}.

  Local Lemma shared_reads_exwp_mono E e Φ Ψ :
    (forall v, Φ v ⊢ Ψ v) -> EXWP e @ E {{ Φ }} ⊢ EXWP e @ E {{ Ψ }}.
  Proof.
    intros Hmono. iLöb as "IH" forall (e). iIntros "Hwp".
    rewrite (exwp_unfold E e Ψ) /exwp_pre. destruct (to_val e) as [v|] eqn:Hv.
    - iEval (rewrite exwp_unfold /exwp_pre Hv) in "Hwp".
      iMod "Hwp" as "HΦ". iModIntro. by iApply Hmono.
    - iEval (rewrite exwp_unfold /exwp_pre Hv) in "Hwp".
      iMod "Hwp" as "[[Hno Hseq] | (%op & %k & %Hcall & Hspec)]"; iModIntro.
      + iLeft. iFrame "Hno". iIntros (m p) "Hm".
        iMod ("Hseq" with "Hm") as "[Hred Hcont]". iModIntro. iFrame "Hred".
        iIntros (T e' m' Hstep). iPoseProof ("Hcont" $! T e' m' with "[%]") as "Hcont"; first done.
        iNext. iMod "Hcont" as (p') "(Hperm & Hm & Hwp)".
        iModIntro. iExists p'. iFrame "Hperm Hm". by iApply "IH".
      + iRight. iExists op, k. iFrame "%".
        iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
        iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
        iModIntro. by iApply "IH".
  Qed.

  Lemma shared_reads_spec :
    ⊢ EXWP shared_reads {{ v, ⌜v = #7⌝ }}.
  Proof.
    rewrite /shared_reads. exwp_bind (Alloc _).
    iApply exwp_alloc. iNext. iIntros (l) "Hl".
    exwp_pure (App _ _). exwp_bind (Write _ _ _).
    iApply (shared_reads_exwp_mono _ _ (fun _ => l ↦ #7)%I with "[Hl]").
    - intros ignored. iIntros "Hl". exwp_pure (App _ _).
      iDestruct "Hl" as "[Hchild Hparent]".
      exwp_bind (Fork _). iApply (conc_wp_fork with "[Hchild]").
      + iNext. iApply (shared_reads_exwp_mono with "[Hchild]").
        * intros v. iIntros "_". done.
        * by iApply (exwp_read_na with "Hchild").
      + iNext. iIntros "_". exwp_pure (App _ _).
        iApply (shared_reads_exwp_mono _ _ (fun w => ⌜w = #7⌝ ∗ l ↦{(1/2)%Qp} #7)%I
          with "[Hparent]").
        * intros v. iIntros "[Hv _]". iExact "Hv".
        * by iApply (exwp_read_na with "Hparent").
    - by iApply (exwp_write_na _ l (LitV LitPoison) (LitV (LitInt 7)) with "Hl").
  Qed.
End shared_reads_proof.

(** The logical example above does not depend on adequacy. The semantic
    corollary covers every Try/Commit interleaving of its two readers. *)
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Corollary shared_reads_adequate Σ `{!lrSqGpreS Σ} m :
  at_sem_adequate [shared_reads] [(fun v => v = #7)] m.
Proof.
  apply (sqex_adequacy Σ). intros. apply shared_reads_spec.
Qed.
