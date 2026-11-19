From Stdlib Require Import List Lia ZArith.
From RICAN Require Import Reader Growth.
Import ListNotations.
Open Scope nat_scope.

Fixpoint read_budgets (budgets : list nat) (input : list Z) : list Z * list Z :=
  match budgets with
  | [] => ([], input)
  | budget :: rest =>
      let '(payload, unread) := transfer budget input in
      let '(later, suffix) := read_budgets rest unread in
      (payload ++ later, suffix)
  end.

Lemma repeat_join : forall (byte : Z) left right,
  repeat byte left ++ repeat byte right = repeat byte (left + right).
Proof.
  intros byte left right.
  induction left as [|left IH]; simpl; [reflexivity | now rewrite IH].
Qed.

Lemma read_budgets_full_prefix : forall byte budgets length tail,
  ordinary byte -> budget_sum budgets <= length ->
  read_budgets budgets (repeat byte length ++ tail) =
  (repeat byte (budget_sum budgets), repeat byte (length - budget_sum budgets) ++ tail).
Proof.
  intros byte budgets; induction budgets as [|budget rest IH]; intros length tail Hbyte Hlength.
  - cbn [read_budgets budget_sum repeat]. now rewrite Nat.sub_0_r.
  - cbn [budget_sum] in Hlength |- *.
    cbn [read_budgets].
    rewrite transfer_full_prefix by (assumption || lia).
    rewrite IH by (assumption || lia).
    rewrite repeat_join, Nat.sub_add_distr.
    reflexivity.
Qed.

Definition grow (initial limit : nat) (input : list Z) : list Z * list Z :=
  read_budgets (loop_schedule initial limit) input.

Theorem growth_result : forall byte initial limit length tail,
  ordinary byte -> 2 <= initial <= limit -> limit - 1 <= length ->
  grow initial limit (repeat byte length ++ tail) =
  (repeat byte (limit - 1), repeat byte (length - (limit - 1)) ++ tail).
Proof.
  intros byte initial limit length tail Hbyte Hcapacity Hlength.
  unfold grow.
  rewrite loop_schedule_matches by exact Hcapacity.
  rewrite read_budgets_full_prefix.
  - now rewrite growth_schedule_budget by lia.
  - exact Hbyte.
  - now rewrite growth_schedule_budget by lia.
Qed.

Theorem final_capacity_equivalence : forall byte initial limit length tail,
  ordinary byte -> 2 <= initial <= limit -> limit - 1 <= length ->
  let input := repeat byte length ++ tail in
  grow initial limit input = split_at (limit - 1) input /\
  grow initial limit input = read limit input.
Proof.
  intros byte initial limit length tail Hbyte Hcapacity Hlength.
  cbn zeta.
  rewrite growth_result, split_full_prefix, read_full_prefix by assumption.
  split; reflexivity.
Qed.

Corollary common_unread_source : forall byte initial limit length tail,
  ordinary byte -> 2 <= initial <= limit -> limit - 1 <= length ->
  let input := repeat byte length ++ tail in
  snd (grow initial limit input) = snd (read limit input).
Proof.
  intros byte initial limit length tail Hbyte Hcapacity Hlength.
  cbn zeta.
  now rewrite (proj2 (final_capacity_equivalence byte initial limit length tail Hbyte Hcapacity Hlength)).
Qed.
