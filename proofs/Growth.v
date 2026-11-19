From Stdlib Require Import Arith Bool List Lia.
Import ListNotations.
Open Scope nat_scope.

Definition next_capacity (current limit : nat) : nat :=
  if limit <=? 2 * current then limit else 2 * current.

Lemma next_capacity_bounds : forall current limit,
  1 <= current -> current < limit ->
  current < next_capacity current limit <= limit.
Proof.
  intros current limit Hpositive Hbelow.
  unfold next_capacity.
  destruct (limit <=? 2 * current) eqn:Hdouble.
  - apply Nat.leb_le in Hdouble. lia.
  - apply Nat.leb_gt in Hdouble. lia.
Qed.

Fixpoint growth_deltas (fuel current limit : nat) : list nat :=
  match fuel with
  | 0 => []
  | S remaining =>
      if current <? limit then
        let next := next_capacity current limit in
        (next - current) :: growth_deltas remaining next limit
      else []
  end.

Definition growth_schedule (initial limit : nat) : list nat :=
  (initial - 1) :: growth_deltas limit initial limit.

Fixpoint budget_sum (budgets : list nat) : nat :=
  match budgets with
  | [] => 0
  | budget :: rest => budget + budget_sum rest
  end.

Lemma growth_deltas_sum : forall fuel current limit,
  1 <= current -> current <= limit -> limit - current <= fuel ->
  budget_sum (growth_deltas fuel current limit) = limit - current.
Proof.
  induction fuel as [|fuel IH]; intros current limit Hpositive Hbound Hfuel.
  - cbn [growth_deltas budget_sum]. lia.
  - cbn [growth_deltas].
    destruct (current <? limit) eqn:Hbelow.
    + apply Nat.ltb_lt in Hbelow.
      pose proof (next_capacity_bounds current limit Hpositive Hbelow) as Hnext.
      cbn [budget_sum].
      rewrite IH by lia.
      lia.
    + apply Nat.ltb_ge in Hbelow.
      cbn [budget_sum]. lia.
Qed.

Theorem growth_schedule_budget : forall initial limit,
  1 <= initial <= limit ->
  budget_sum (growth_schedule initial limit) = limit - 1.
Proof.
  intros initial limit [Hpositive Hbound].
  unfold growth_schedule.
  cbn [budget_sum].
  rewrite growth_deltas_sum by lia.
  lia.
Qed.

Record growth_state := {
  line_capacity : nat;
  write_offset : nat
}.

Record resize_result := {
  state_after : growth_state;
  call_capacity : nat;
  payload_budget : nat
}.

Definition filled_state (capacity : nat) : growth_state :=
  {| line_capacity := capacity; write_offset := capacity - 1 |}.

Definition resize_enabled (limit : nat) (state : growth_state) (last_is_lf : bool) : bool :=
  (line_capacity state <? limit)
    && (write_offset state =? line_capacity state - 1)
    && negb last_is_lf.

Definition resize (limit : nat) (state : growth_state) : resize_result :=
  let next := next_capacity (line_capacity state) limit in
  let room := next - write_offset state in
  let budget := room - 1 in
  {| state_after := {| line_capacity := next; write_offset := write_offset state + budget |};
     call_capacity := room;
     payload_budget := budget |}.

Theorem resize_exact : forall current limit,
  2 <= current -> current < limit ->
  let next := next_capacity current limit in
  let result := resize limit (filled_state current) in
  call_capacity result = next - current + 1 /\
  payload_budget result = next - current /\
  state_after result = filled_state next.
Proof.
  intros current limit Hcapacity Hbelow.
  pose proof (next_capacity_bounds current limit ltac:(lia) Hbelow) as Hnext.
  cbn [resize filled_state line_capacity write_offset state_after call_capacity payload_budget].
  repeat split; try lia.
  unfold filled_state.
  f_equal. lia.
Qed.

Lemma resize_enabled_filled : forall limit current,
  resize_enabled limit (filled_state current) false = (current <? limit).
Proof.
  intros limit current.
  unfold resize_enabled, filled_state.
  simpl. now rewrite Nat.eqb_refl, !andb_true_r.
Qed.

(* Only the full-read branch enters the modeled resize loop. *)
Fixpoint resize_budgets (fuel limit : nat) (state : growth_state) : list nat :=
  match fuel with
  | 0 => []
  | S remaining =>
      if resize_enabled limit state false then
        let result := resize limit state in
        payload_budget result :: resize_budgets remaining limit (state_after result)
      else []
  end.

Lemma resize_budgets_match : forall fuel current limit,
  2 <= current <= limit ->
  resize_budgets fuel limit (filled_state current) = growth_deltas fuel current limit.
Proof.
  induction fuel as [|fuel IH]; intros current limit Hbounds.
  - reflexivity.
  - cbn [resize_budgets growth_deltas].
    rewrite resize_enabled_filled.
    destruct (current <? limit) eqn:Hbelow; [|reflexivity].
    apply Nat.ltb_lt in Hbelow.
    pose proof (next_capacity_bounds current limit ltac:(lia) Hbelow) as Hnext.
    pose proof (resize_exact current limit ltac:(lia) Hbelow) as [_ [Hbudget Hstate]].
    rewrite Hbudget, Hstate.
    f_equal. apply IH. lia.
Qed.

Definition loop_schedule (initial limit : nat) : list nat :=
  (initial - 1) :: resize_budgets limit limit (filled_state initial).

Theorem loop_schedule_matches : forall initial limit,
  2 <= initial <= limit ->
  loop_schedule initial limit = growth_schedule initial limit.
Proof.
  intros initial limit Hbounds.
  unfold loop_schedule, growth_schedule.
  now rewrite resize_budgets_match.
Qed.
