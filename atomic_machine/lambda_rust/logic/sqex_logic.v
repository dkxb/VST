(** The sequential lambda-Rust logic with parameterized ExtCallSems. *)

From iris.program_logic Require Export weakestpre.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(* TODO adequacy need to be proved
   with a concrete language and ExtCallSems. *)
Class ExtCallSems `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout Expr) :=
  extcall_sems : @atomic_op Loc Val Layout Expr ->
    Mem -> option Val -> Mem ->
    list (@sqlang_thrd_st _ _ _ _ _ _ _ L) -> Prop.

Section ext_step.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr, !ExtCallSems L}.

  Local Notation C := sqlang_thrd_st.

  (** Write-version effects of an external operation. These annotate the
      parameterized call semantics; they do not change [lr_step]. Failed CAS
      operations do not write, while successful CAS and stores advance every
      location covered by their layout, including same-value stores. *)
  Inductive extcall_events : @atomic_op Loc Val Layout Expr ->
      option Val -> list (@mem_ev Loc) -> Prop :=
  | ExtLoadEvents ly l ov : extcall_events (ALoad ly l) ov []
  | ExtStoreEvents ly l v ov :
      extcall_events (AStore ly l v) ov (atomic_machine.Write <$> layout_to_locs l ly)
  | ExtCASSuccessEvents ly l v v' :
      extcall_events (ACAS ly l v v') (Some sqlang_true_val)
        (atomic_machine.Write <$> layout_to_locs l ly)
  | ExtCASOtherEvents ly l v v' ov :
      ov ≠ Some sqlang_true_val -> extcall_events (ACAS ly l v v') ov []
  | ExtSpawnEvents e ov : extcall_events (ASpawn e) ov [].

  (** A thread at an atomic operation performs it according to
      [extcall_sems], continues with the returned value, and spawns [efs]. *)
  Inductive ext_step : C -> Mem -> list (@mem_ev Loc) -> C -> Mem -> list C -> Prop :=
  | ExtStep c op K m ov m' c' efs T :
      sqlang_at_external c op K ->
      extcall_sems op m ov m' efs ->
      extcall_events op ov T ->
      sqlang_after_external c ov c' ->
      ext_step c m T c' m' efs.
End ext_step.

Section exwp_pre.
Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr,
  !ExtCallSems L, !invGS Σ}.

Local Notation C := sqlang_thrd_st.
Local Existing Instance L.

(** Based on iris wp, but sequential steps use basic updates, which can update 
    heap ghost state but cannot open invariants; only (atomic) external calls
    (including [Fork]) have an fupd and can open invariants.
    The state interpretation receives a per-location version map. The actual
    step events determine its successor via [sq_versions_after]; this forces
    writes to increment their versions without recording an execution history.
    TODO support non-atomic external calls (which should not have fupd) *)
Definition exwp_pre (value_of : C -> option Val) (state_interp : Mem -> (Loc -> nat) -> iProp Σ)
    (exwp : coPset -d> C -d> (Val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> C -d> (Val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match value_of e1 with
  | Some v => |==> Φ v
  | None => |==>
      (∀ m1 ver_map, state_interp m1 ver_map ==∗
        ⌜exists T e2 m2, sqlang_step e1 m1 T e2 m2⌝ ∗
        ∀ T e2 m2, ⌜sqlang_step e1 m1 T e2 m2⌝ -∗ ▷ |==>
          state_interp m2 (sq_versions_after T ver_map) ∗ exwp E e2 Φ) ∨
      (⌜exists op k, sqlang_at_external e1 op k⌝ ∗
        ∀ m1 ver_map, state_interp m1 ver_map ={E,∅}=∗
          ⌜exists T e2 m2 efs, ext_step e1 m1 T e2 m2 efs⌝ ∗
          ∀ T e2 m2 efs, ⌜ext_step e1 m1 T e2 m2 efs⌝ -∗
            |={∅}▷=> |={∅,E}=> state_interp m2 (sq_versions_after T ver_map) ∗ exwp E e2 Φ ∗
              [∗ list] ef ∈ efs, exwp ⊤ ef (λ _, True))
  end%I.

Global Instance exwp_pre_contractive value_of state_interp :
  Contractive (exwp_pre value_of state_interp).
Proof.
  rewrite /exwp_pre /= => n exwp exwp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.
End exwp_pre.

Local Existing Instance lrSqGS_invGS.

Local Definition exwp_def `{!ExtCallSems lr_language, !lrSqGS Σ} :
  coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ :=
  fixpoint (exwp_pre (L := lr_language) to_val sq_heap_gen).
Local Definition exwp_aux : seal (@exwp_def). Proof. by eexists. Qed.
Definition exwp := exwp_aux.(unseal).
Global Arguments exwp {_ Σ _} E e%_E Φ%_I.

Local Lemma exwp_unseal `{!ExtCallSems lr_language, !lrSqGS Σ} :
  exwp = @exwp_def _ Σ _.
Proof. rewrite -exwp_aux.(seal_eq) //. Qed.

Notation "'EXWP' e @ E {{ Φ } }" := (exwp E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EXWP' e {{ Φ } }" := (exwp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EXWP' e @ E {{ v , Q } }" := (exwp E e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'EXWP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EXWP' e {{ v , Q } }" := (exwp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'EXWP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(** These triples explicitly use [EXWP], independently of Iris's [Wp] instance. *)
Notation "'{{{' P } } } 'EXWP' e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ EXWP e @ E {{ Φ }})%I
  (at level 20,
   format "'[hv' {{{  '[' P  ']' } } }  '/  ' 'EXWP'  e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } 'EXWP' e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, ⊢ P -∗ ▷ (Q -∗ Φ pat%V) -∗ EXWP e @ E {{ Φ }}) : stdpp_scope.

Section exwp.
  Context `{!ExtCallSems lr_language, !lrSqGS Σ}.

  Lemma exwp_unfold E e Φ :
    EXWP e @ E {{ Φ }} ⊣⊢ exwp_pre (L := lr_language) to_val sq_heap_gen exwp E e Φ.
  Proof.
    rewrite exwp_unseal.
    apply (fixpoint_unfold (exwp_pre (L := lr_language) to_val sq_heap_gen)).
  Qed.

  Lemma exwp_value_bupd E v Φ : EXWP of_val v @ E {{ Φ }} ⊣⊢ |==> Φ v.
  Proof. by rewrite exwp_unfold /exwp_pre to_of_val. Qed.

  (** Ordinary steps have no fancy update, even before establishing reducibility. *)
  Lemma exwp_seq_unfold E e Φ :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    EXWP e @ E {{ Φ }} ⊣⊢
      (∀ m1 ver_map, sq_heap_gen m1 ver_map ==∗
        ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
        ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
          sq_heap_gen m2 (sq_versions_after T ver_map) ∗ EXWP e2 @ E {{ Φ }}).
  Proof.
    intros Hv Hext. rewrite exwp_unfold /exwp_pre Hv.
    iSplit; last by iIntros "H"; iModIntro; iLeft.
    iIntros "H" (m ver_map) "Hm". iMod "H" as "[Hseq | [%Hcall _]]".
    - by iApply "Hseq".
    - destruct Hcall as (op & k & Hcall). by exfalso; eapply Hext.
  Qed.

  Lemma exwp_lift_step E e Φ :
    to_val e = None ->
    (∀ m1 ver_map, sq_heap_gen m1 ver_map ==∗
      ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
      ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
        sq_heap_gen m2 (sq_versions_after T ver_map) ∗ EXWP e2 @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof. intros Hv. rewrite exwp_unfold /exwp_pre Hv. iIntros "H". iModIntro. by iLeft. Qed.

  Lemma exwp_lift_ext_step E e op k Φ :
    lr_external e op k ->
    (∀ m1 ver_map, sq_heap_gen m1 ver_map ={E,∅}=∗
      ⌜exists T e2 m2 efs, ext_step (L := lr_language) e m1 T e2 m2 efs⌝ ∗
      ∀ T e2 m2 efs, ⌜ext_step (L := lr_language) e m1 T e2 m2 efs⌝ -∗
        |={∅}▷=> |={∅,E}=> sq_heap_gen m2 (sq_versions_after T ver_map) ∗ EXWP e2 @ E {{ Φ }} ∗
          [∗ list] ef ∈ efs, EXWP ef {{ _, True }}) ⊢
      EXWP e @ E {{ Φ }}.
  Proof.
    intros Hext. assert (to_val e = None) as Hv.
    { destruct Hext as [K e op k Hhead]. apply fill_not_val. by destruct Hhead. }
    rewrite exwp_unfold /exwp_pre Hv.
    iIntros "Hstep". iModIntro. iRight. iSplit; [ eauto | done ].
  Qed.

  (** A write cannot preserve a fraction framed outside its EXWP: the
      successor heap must advance the version at that location. The
      contradiction is guarded by the same logical step as that update;
      no immediate ownership-extraction property is required. *)
  Lemma sqex_write_frame E e Φ m ver_map T e' m' l q v :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    lr_step e m T e' m' -> lr_write_event l ∈ T ->
    sq_heap_gen m ver_map -∗ EXWP e @ E {{ Φ }} -∗ l ↦{q} v -∗ ▷ False.
  Proof.
    intros Hv Hext Hstep Hwrite.
    destruct (lr_step_write_footprint _ _ _ _ _ _ Hstep Hwrite)
      as (old & new & Hold & -> & Hmem).
    iIntros "Hm Hwp (%n & Hl)".
    iDestruct (sq_heap_gen_version with "Hm Hl") as %Hbefore.
    rewrite (exwp_seq_unfold _ _ _ Hv Hext).
    iMod ("Hwp" with "Hm") as "[_ Hstep]".
    iPoseProof ("Hstep" $! _ _ _ with "[%]") as "Hstep"; first exact Hstep.
    iNext. iMod "Hstep" as "[Hm _]".
    iDestruct (sq_heap_gen_version with "Hm Hl") as %Hafter.
    rewrite /sq_versions_after /= /sq_count_next decide_True in Hafter; last done.
    iPureIntro. lia.
  Qed.
End exwp.
