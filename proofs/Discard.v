From Stdlib Require Import Arith List Lia ZArith.
From RICAN Require Import Reader Handoff.
Import ListNotations.
Open Scope nat_scope.

Fixpoint discard_full_reads (capacity count : nat) (input : list Z) : list Z :=
  match count with
  | 0 => input
  | S remaining =>
      discard_full_reads capacity remaining (snd (read capacity input))
  end.

Lemma discard_full_prefix : forall byte capacity count length tail,
  ordinary byte -> 2 <= capacity -> (capacity - 1) * count <= length ->
  discard_full_reads capacity count (repeat byte length ++ tail) =
  repeat byte (length - (capacity - 1) * count) ++ tail.
Proof.
  intros byte capacity count; induction count as [|count IH];
    intros length tail Hbyte Hcapacity Hlength.
  - cbn [discard_full_reads]. now rewrite Nat.mul_0_r, Nat.sub_0_r.
  - rewrite Nat.mul_succ_r in Hlength.
    cbn [discard_full_reads].
    rewrite read_full_prefix by (assumption || nia).
    cbn [snd].
    rewrite IH by (assumption || nia).
    now rewrite Nat.mul_succ_r,
      (Nat.add_comm ((capacity - 1) * count) (capacity - 1)), Nat.sub_add_distr.
Qed.

Definition selected_discard (capacity ordinary_length : nat) (input : list Z)
  : list Z * list Z :=
  let count := ordinary_length / (capacity - 1) in
  read capacity (discard_full_reads capacity count input).

Lemma selected_discard_visible_length : forall byte capacity length tail,
  ordinary byte -> 2 <= capacity ->
  visible_length
    (destination (fst (selected_discard capacity length (repeat byte length ++ terminator :: tail)))) =
  length mod (capacity - 1).
Proof.
  intros byte capacity length tail Hbyte Hcapacity.
  assert (Hpositive : capacity - 1 <> 0) by lia.
  pose proof (Nat.div_mod length (capacity - 1) Hpositive) as Hdivision.
  pose proof (Nat.mod_upper_bound length (capacity - 1) Hpositive) as Hremainder.
  unfold selected_discard.
  rewrite discard_full_prefix by (assumption || nia).
  replace (length - (capacity - 1) * (length / (capacity - 1)))
    with (length mod (capacity - 1)) by lia.
  apply read_visible_length; assumption.
Qed.

Theorem discard_capacity_law : forall byte initial limit capacity length tail,
  ordinary byte -> 2 <= initial <= limit -> 2 <= capacity -> limit - 1 <= length ->
  let input := repeat byte length ++ terminator :: tail in
  let remaining := length - (limit - 1) in
  let grown := selected_discard capacity remaining (snd (grow initial limit input)) in
  let fixed := selected_discard capacity remaining (snd (read limit input)) in
  grown = fixed /\
  visible_length (destination (fst grown)) = remaining mod (capacity - 1).
Proof.
  intros byte initial limit capacity length tail Hbyte Hbounds Hcapacity Hlength.
  cbn zeta.
  split.
  - rewrite (common_unread_source byte initial limit length (terminator :: tail))
      by assumption.
    reflexivity.
  - rewrite growth_result by assumption.
    apply selected_discard_visible_length; assumption.
Qed.

Definition last_index (visible : nat) : option nat :=
  match visible with
  | 0 => None
  | S index => Some index
  end.

Corollary discard_last_index : forall byte initial limit capacity length tail,
  ordinary byte -> 2 <= initial <= limit -> 2 <= capacity -> limit - 1 <= length ->
  let input := repeat byte length ++ terminator :: tail in
  let remaining := length - (limit - 1) in
  let result := selected_discard capacity remaining (snd (grow initial limit input)) in
  let visible := visible_length (destination (fst result)) in
  match remaining mod (capacity - 1) with
  | 0 => last_index visible = None
  | S index => last_index visible = Some index /\ index < capacity
  end.
Proof.
  intros byte initial limit capacity length tail Hbyte Hbounds Hcapacity Hlength.
  cbn zeta.
  pose proof (proj2 (discard_capacity_law byte initial limit capacity length tail
    Hbyte Hbounds Hcapacity Hlength)) as Hvisible.
  rewrite Hvisible.
  pose proof (Nat.mod_upper_bound (length - (limit - 1)) (capacity - 1) ltac:(lia)) as Hremainder.
  destruct ((length - (limit - 1)) mod (capacity - 1)) as [|index].
  - reflexivity.
  - split; [reflexivity | lia].
Qed.
