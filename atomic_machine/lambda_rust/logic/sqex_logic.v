(** The sequential lambda-Rust logic parameterized by logical external specifications. *)

From iris.program_logic Require Export weakestpre.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** A collection of Hoare specifications. The argument type contains each
    operation's logical parameters. Preconditions may require verification
    of spawned threads. EXWP supplies their WPs under a later; the
    precondition itself is required now, inside the opening fancy update. *)
Class ExtCallSpecs `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout Expr)
    (Σ : gFunctors) := {
  ext_spec_args : @atomic_op Loc Val Layout Expr -> Type;
  ext_spec_pre : forall op, ext_spec_args op ->
    ((@sqlang_thrd_st _ _ _ _ _ _ _ L) -d> iPropO Σ) -n> iPropO Σ;
  ext_spec_post : forall op, ext_spec_args op -> option Val -> iProp Σ
}.

Section exwp_pre.
Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr, !invGS Σ}.
Context (specs : ExtCallSpecs L Σ).
Local Existing Instance specs.
Local Existing Instance L.
Local Notation C := sqlang_thrd_st.

(** Sequential steps use basic updates and obey [perm_step]. External calls
    consume a declared precondition and resume from its postcondition, with
    fancy updates for invariant access and ownership transfer. The sequential
    branch excludes external calls so their specifications can be exposed
    without supplying a physical heap. *)
Definition exwp_pre (value_of : C -> option Val)
    (state_interp : Mem -> gmap Loc Qp -> iProp Σ)
    (exwp : coPset -d> C -d> (Val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> C -d> (Val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match value_of e1 with
  | Some v => |==> Φ v
  | None => |==>
      (⌜forall op k, ~ sqlang_at_external e1 op k⌝ ∗
       ∀ m1 h1, state_interp m1 h1 ==∗
        ⌜exists T e2 m2, sqlang_step e1 m1 T e2 m2⌝ ∗
        ∀ T e2 m2, ⌜sqlang_step e1 m1 T e2 m2⌝ -∗ ▷ |==>
          ∃ h2, ⌜perm_step T h1 h2⌝ ∗
            state_interp m2 h2 ∗ exwp E e2 Φ) ∨
      (∃ op k, ⌜sqlang_at_external e1 op k⌝ ∗
        |={E,∅}=> ∃ x : ext_spec_args op,
          ext_spec_pre op x (λ ef, ▷ exwp ⊤ ef (λ _, True)) ∗
          ▷ (∀ ov, ext_spec_post op x ov -∗
            |={∅,E}=> exwp E (k ov) Φ))
  end%I.

Global Instance exwp_pre_contractive value_of state_interp :
  Contractive (exwp_pre value_of state_interp).
Proof.
  rewrite /exwp_pre /= => n exwp exwp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); first [apply Hwp | intros ef; f_contractive; apply Hwp].
Qed.
End exwp_pre.

Local Existing Instance lrSqGS_invGS.

Local Definition exwp_def `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} :
  coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ :=
  fixpoint (exwp_pre _ to_val sq_heap_gen).
Local Definition exwp_aux : seal (@exwp_def). Proof. by eexists. Qed.
Definition exwp := exwp_aux.(unseal).
Global Arguments exwp {Σ _ _} E e%_E Φ%_I.

Local Lemma exwp_unseal `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ} :
  exwp = @exwp_def Σ _ _.
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
  Context `{!lrSqGS Σ, !ExtCallSpecs lr_language Σ}.

  Lemma exwp_unfold E e Φ :
    EXWP e @ E {{ Φ }} ⊣⊢ exwp_pre _ to_val sq_heap_gen exwp E e Φ.
  Proof.
    rewrite exwp_unseal.
    apply (fixpoint_unfold (exwp_pre _ to_val sq_heap_gen)).
  Qed.

  Lemma exwp_value_bupd E v Φ : EXWP of_val v @ E {{ Φ }} ⊣⊢ |==> Φ v.
  Proof. by rewrite exwp_unfold /exwp_pre to_of_val. Qed.

  Lemma exwp_seq_unfold E e Φ :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    EXWP e @ E {{ Φ }} ⊣⊢
      (∀ m1 h, sq_heap_gen m1 h ==∗
        ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
        ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
          ∃ h2, ⌜perm_step T h h2⌝ ∗ sq_heap_gen m2 h2 ∗ EXWP e2 @ E {{ Φ }}).
  Proof.
    intros Hv Hext. rewrite exwp_unfold /exwp_pre Hv.
    iSplit.
    - iIntros "H" (m h) "Hm".
      iMod "H" as "[[_ Hseq] | (%op & %k & %Hcall & _)]".
      + by iApply "Hseq".
      + exfalso. by eapply Hext.
    - iIntros "H !>". iLeft. iFrame. done.
  Qed.

  (** Permission checks can be recovered from an arbitrary sequential EXWP
      proof, under the same later that guards its successor state. *)
  Lemma exwp_step_permissions E e Φ m h T e' m' :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    lr_step e m T e' m' ->
    sq_heap_gen m h -∗ EXWP e @ E {{ Φ }} -∗
      ▷ ⌜exists h', perm_step T h h'⌝.
  Proof.
    intros Hv Hext Hstep. iIntros "Hm Hwp".
    rewrite (exwp_seq_unfold _ _ _ Hv Hext).
    iMod ("Hwp" with "Hm") as "[_ Hstep]".
    iPoseProof ("Hstep" $! T e' m' with "[%]") as "Hstep"; first done.
    iNext. iMod "Hstep" as (h') "(%Hperm & _)". eauto.
  Qed.

  Lemma exwp_lift_step E e Φ :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    (∀ m1 h, sq_heap_gen m1 h ==∗
      ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
      ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
        ∃ h2, ⌜perm_step T h h2⌝ ∗ sq_heap_gen m2 h2 ∗ EXWP e2 @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof. intros Hv Hext. by rewrite (exwp_seq_unfold _ _ _ Hv Hext). Qed.

  Lemma exwp_lift_external E e op k Φ :
    lr_external e op k ->
    (|={E,∅}=> ∃ x : ext_spec_args op,
      ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) ∗
      ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> EXWP k ov @ E {{ Φ }})) ⊢
    EXWP e @ E {{ Φ }}.
  Proof.
    intros Hext. assert (to_val e = None) as Hv.
    { destruct Hext as [K e op k Hhead]. apply fill_not_val. by destruct Hhead. }
    rewrite exwp_unfold /exwp_pre Hv.
    iIntros "Hspec !>". iRight. iExists op, k. by iFrame.
  Qed.
End exwp.
