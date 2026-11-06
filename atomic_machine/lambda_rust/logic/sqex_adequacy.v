(** Adequacy of the lifted sequential logic over the atomic machine semantics
    of lambda-Rust. *)

From stdpp Require Import relations.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_adequacy.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Import ListNotations.

(** The external-call semantics.  *)
Class satisfy_conc_triples Σ `{!ExtCallSems lr_language} : Prop := {
  conc_wp_read_sc : forall `{!lrSqGS Σ} E l q v,
    {{{ ▷ l ↦{q} v }}} EXWP (Read ScOrd (Lit $ LitLoc l) : sq_expr) @ E
    {{{ RET (v : sq_val); l ↦{q} v }}};
  conc_wp_write_sc : forall `{!lrSqGS Σ} E l (e : sq_expr) v v',
    IntoVal e v ->
    {{{ ▷ l ↦ v' }}} EXWP (Write ScOrd (Lit $ LitLoc l) e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); l ↦ v }}};
  conc_wp_fork : forall `{!lrSqGS Σ} E (e : sq_expr),
    {{{ ▷ EXWP e {{ _, True }} }}} EXWP (Fork e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); True }}}
  (* other atomic operations *)
}.

(**  every allocated location is unreserved. *)
Definition sq_mu (m : lr_mem) : rw_map := (fun _ => Rst 0) <$> m.

Definition sqex_pool (tp : list sq_expr) : tpool :=
  map_seq 0%nat ((fun e => Running e []) <$> tp).

(** execution is safe and mem terminates in a state satisfying the postconditions. FIXME what should the initial rw_map be? *)
Definition at_sem_adequate (tp : list sq_expr) (φs : list (sq_val -> Prop)) (m : lr_mem) : Prop :=
  forall tp' m' mu',
    am_steps (AMCfg (sqex_pool tp) m (sq_mu m)) (AMCfg tp' m' mu') ->
    (forall i t, tp' !! i = Some t -> am_not_stuck t m' mu') /\
    (forall i e v φ, tp' !! i = Some (Running e []) -> to_val e = Some v ->
       φs !! i = Some φ -> φ v).

(** TODO do iLob here, figure out IH *)
(* EXWP uses basic updates for normal steps and allows fupd around external calls and spawning. *)
Theorem sqex_adequacy Σ
    `{!lrSqGpreS Σ}
    (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ} `{!ExtCallSems lr_language} `{!satisfy_conc_triples Σ},
  ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
Admitted.
