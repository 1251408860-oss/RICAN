From Stdlib Require Import List Lia ZArith.
Import ListNotations.
Open Scope nat_scope.

Definition line_feed : Z := 10%Z.
Definition terminator : Z := 0%Z.
Definition ordinary (byte : Z) : Prop :=
  byte <> terminator /\ byte <> line_feed.

Fixpoint transfer (budget : nat) (input : list Z) : list Z * list Z :=
  match budget with
  | 0 => ([], input)
  | S remaining_budget =>
      match input with
      | [] => ([], [])
      | byte :: remaining =>
          if Z.eqb byte line_feed then ([byte], remaining)
          else
            let '(copied, unread) := transfer remaining_budget remaining in
            (byte :: copied, unread)
      end
  end.

Definition read (capacity : nat) (input : list Z) : list Z * list Z :=
  transfer (capacity - 1) input.

Definition destination (payload : list Z) : list Z :=
  payload ++ [terminator].

Definition call (capacity : nat) (input : list Z) : option (list Z * list Z) :=
  match capacity, input with
  | S (S _), _ :: _ =>
      let result := read capacity input in
      Some (destination (fst result), snd result)
  | _, _ => None
  end.

Definition split_at (index : nat) (input : list Z) : list Z * list Z :=
  (firstn index input, skipn index input).

Fixpoint visible_length (bytes : list Z) : nat :=
  match bytes with
  | [] => 0
  | byte :: rest =>
      if Z.eqb byte terminator then 0 else S (visible_length rest)
  end.

Lemma call_success : forall capacity input,
  2 <= capacity -> input <> [] ->
  call capacity input =
  Some (destination (fst (read capacity input)), snd (read capacity input)).
Proof.
  intros [|[|capacity]] input Hcapacity Hinput; try lia.
  destruct input; [contradiction | reflexivity].
Qed.

Lemma transfer_full_prefix : forall byte budget length tail,
  ordinary byte -> budget <= length ->
  transfer budget (repeat byte length ++ tail) =
  (repeat byte budget, repeat byte (length - budget) ++ tail).
Proof.
  intros byte budget; induction budget as [|budget IH];
    intros length tail Hbyte Hlength.
  - cbn [transfer repeat]. now rewrite Nat.sub_0_r.
  - destruct length as [|length]; [lia |].
    assert (Hline : Z.eqb byte line_feed = false)
      by (apply Z.eqb_neq; exact (proj2 Hbyte)).
    cbn [repeat app transfer].
    rewrite Hline, IH by (assumption || lia).
    reflexivity.
Qed.

Lemma read_full_prefix : forall byte capacity length tail,
  ordinary byte -> capacity - 1 <= length ->
  read capacity (repeat byte length ++ tail) =
  (repeat byte (capacity - 1), repeat byte (length - (capacity - 1)) ++ tail).
Proof.
  intros. apply transfer_full_prefix; assumption.
Qed.

Lemma split_full_prefix : forall byte count length tail,
  count <= length ->
  split_at count (repeat byte length ++ tail) =
  (repeat byte count, repeat byte (length - count) ++ tail).
Proof.
  intros byte count; induction count as [|count IH]; intros length tail Hlength.
  - unfold split_at. cbn [firstn skipn repeat]. now rewrite Nat.sub_0_r.
  - destruct length as [|length]; [lia |].
    unfold split_at.
    cbn [repeat app firstn skipn].
    specialize (IH length tail ltac:(lia)).
    unfold split_at in IH.
    injection IH as Hprefix Htail.
    now rewrite Hprefix, Htail.
Qed.

Lemma visible_length_at_terminator : forall byte length tail,
  ordinary byte -> visible_length (repeat byte length ++ terminator :: tail) = length.
Proof.
  intros byte length; induction length as [|length IH]; intros tail Hbyte.
  - cbn [repeat app visible_length]. now rewrite Z.eqb_refl.
  - assert (Hzero : Z.eqb byte terminator = false)
      by (apply Z.eqb_neq; exact (proj1 Hbyte)).
    cbn [repeat app visible_length].
    rewrite Hzero, IH by assumption.
    reflexivity.
Qed.

Lemma transfer_reaches_terminator : forall byte length budget tail,
  ordinary byte -> length < budget ->
  exists copied unread,
    transfer budget (repeat byte length ++ terminator :: tail) =
    (repeat byte length ++ terminator :: copied, unread).
Proof.
  intros byte length; induction length as [|length IH]; intros budget tail Hbyte Hbudget.
  - destruct budget as [|budget]; [lia |].
    cbn [repeat app transfer].
    assert (Hline : Z.eqb terminator line_feed = false) by reflexivity.
    rewrite Hline.
    destruct (transfer budget tail) as [copied unread].
    exists copied, unread. reflexivity.
  - destruct budget as [|budget]; [lia |].
    destruct (IH budget tail Hbyte ltac:(lia)) as [copied [unread Hread]].
    assert (Hline : Z.eqb byte line_feed = false)
      by (apply Z.eqb_neq; exact (proj2 Hbyte)).
    cbn [repeat app transfer].
    rewrite Hline, Hread.
    exists copied, unread. reflexivity.
Qed.

Lemma read_visible_length : forall byte capacity length tail,
  ordinary byte -> length < capacity - 1 ->
  visible_length (destination (fst (read capacity (repeat byte length ++ terminator :: tail)))) =
  length.
Proof.
  intros byte capacity length tail Hbyte Hlength.
  unfold read.
  destruct (transfer_reaches_terminator byte length (capacity - 1) tail Hbyte Hlength)
    as [copied [unread Htransfer]].
  rewrite Htransfer.
  unfold destination. cbn [fst].
  rewrite <- app_assoc. cbn [app].
  apply visible_length_at_terminator. exact Hbyte.
Qed.
