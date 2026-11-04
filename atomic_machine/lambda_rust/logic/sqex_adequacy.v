(** Adequacy of the lifted sequential logic over the atomic machine semantics
    of lambda-Rust. *)

From stdpp Require Import relations.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_adequacy.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Import ListNotations.

(** The external-call semantics validates the SC-read, SC-write, and spawn
    rules for every heap ghost-state instance. Other atomic operations are
    left open for now. *)
Class satisfy_conc_triples Σ `{!ExtCallSems lr_language} : Prop := {
  conc_wp_read_sc : forall `{!lrSqGS Σ} E l q v,
    {{{ ▷ l ↦{q} v }}} (Read ScOrd (Lit $ LitLoc l) : sqex_expr) @ E
    {{{ RET (v : sqex_val); l ↦{q} v }}};
  conc_wp_write_sc : forall `{!lrSqGS Σ} E l (e : sqex_expr) v v',
    IntoVal e v ->
    {{{ ▷ l ↦ v' }}} (Write ScOrd (Lit $ LitLoc l) e : sqex_expr) @ E
    {{{ RET (LitV LitPoison : sqex_val); l ↦ v }}};
  conc_wp_fork : forall `{!lrSqGS Σ} E (e : sqex_expr),
    {{{ ▷ WP e {{ _, True }} }}} (Fork e : sqex_expr) @ E
    {{{ RET (LitV LitPoison : sqex_val); True }}}
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
(* WP needs to be changed: don't allow fupd around normal steps, only between steps and around atomic steps. *)
Theorem sqex_adequacy Σ
    `{!lrSqGpreS Σ}
    (e : sqex_expr) (φ : sqex_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ} `{!ExtCallSems lr_language} `{!satisfy_conc_triples Σ},
  ⊢ WP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
Admitted.
