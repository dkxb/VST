(** The successor permission map is determined by the sequential trace. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_frame.
Require Import VST.atomic_machine.atomic_machine.

Set Default Proof Using "Type".

Definition sqex_perm_after_event (ev : @mem_ev loc) (p : perm_map) : perm_map :=
  match ev with
  | atomic_machine.Read _ | atomic_machine.Write _ => p
  | atomic_machine.Alloc l => <[l := 1%Qp]> p
  | atomic_machine.Free l => delete l p
  end.

Fixpoint sqex_perm_after (T : list (@mem_ev loc)) (p : perm_map) : perm_map :=
  match T with
  | [] => p
  | ev :: T => sqex_perm_after T (sqex_perm_after_event ev p)
  end.

Lemma sqex_perm_step_result T p p' :
  perm_step T p p' -> p' = sqex_perm_after T p.
Proof.
  induction 1 as [p|ev T p1 p2 p3 Hev Htail IH]; first done.
  simpl. rewrite IH. by destruct Hev.
Qed.

Lemma sqex_perm_step_after T p p' :
  perm_step T p p' -> perm_step T p (sqex_perm_after T p).
Proof. intros Hstep. by rewrite -(sqex_perm_step_result _ _ _ Hstep). Qed.
