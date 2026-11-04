(** The sequential lambda-Rust logic with parameterized ExtCallSems. *)

From iris.program_logic Require Export weakestpre.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

Class ExtCallSems `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout) :=
  extcall_sems : @atomic_op Loc Val Layout -> Mem -> option Val -> Mem -> Prop.

Section ext_step.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout, !ExtCallSems L}.

  Local Notation C := sqlang_thrd_st.

  (** A thread at an atomic operation performs it according to
      [extcall_sems], and continues with the returned value. *)
  Inductive ext_step : C -> Mem -> C -> Mem -> Prop :=
  | ExtStep c op K m ov m' c' :
      sqlang_at_external c op K ->
      extcall_sems op m ov m' ->
      sqlang_after_external c ov c' ->
      ext_step c m c' m'.
End ext_step.

(** * The language *)
Definition sqex_expr : Type := sq_expr.
Definition sqex_val : Type := sq_val.

Section sqex_language.
  Context `{!ExtCallSems lr_language}.

  (** A single-thread step emits no observations and spawns no threads. *)
  Inductive sqex_step
      : sqex_expr -> lr_mem -> list Empty_set -> sqex_expr -> lr_mem -> list sqex_expr -> Prop :=
  | SqexSeqStep m e T e' m' :
      lr_step e m T e' m' ->
      sqex_step e m [] e' m' []
  | SqexExtStep m e e' m' :
      ext_step (L := lr_language) e m e' m' ->
      sqex_step e m [] e' m' [].

  Lemma sqex_val_stuck e m κ e' m' efs :
    sqex_step e m κ e' m' efs -> to_val e = None.
  Proof.
    destruct 1 as [m e T e' m' Hstep | m e e' m' Hstep].
    - destruct Hstep as [K e1 m1 T e2 m2 Hhead].
      apply fill_not_val. by destruct Hhead.
    - destruct Hstep as [e op k m ov m' e' Hext Hsem Hafter].
      destruct Hext as [K e op k Hhead].
      apply fill_not_val. by destruct Hhead.
  Qed.

  Lemma sqex_lang_mixin :
    @LanguageMixin sqex_expr sqex_val lr_mem Empty_set of_val to_val sqex_step.
  Proof.
    split.
    - apply to_of_val.
    - apply of_to_val.
    - apply sqex_val_stuck.
  Qed.

  Canonical Structure sqex_lang := Language sqex_lang_mixin.
End sqex_language.

(** Reuse the sequential logic's heap interpretation for Iris's [WP]. *)
Global Instance lrSqExGS_irisGS `{!ExtCallSems lr_language, !lrSqGS Σ} :
    irisGS sqex_lang Σ := {
  iris_invGS := lrSqGS_invGS;
  state_interp m _ _ _ := sq_heap m;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
