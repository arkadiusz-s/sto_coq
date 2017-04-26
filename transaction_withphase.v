Require Import Bool Arith List Omega.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require FMapList.
Require FMapFacts.
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Sorting.Permutation.
Import ListNotations.
Module NatMap := FMapList.Make Nat_as_OT.

Definition address := nat.
Definition version := nat.
Definition value := nat.
Definition lock := bool.
Definition variable := nat.
Definition store := NatMap.t value.
Definition heap :=  address -> option (value * lock * version).
Definition tid := nat.


Ltac myauto :=
  repeat match goal with
  | |- context[_] =>
      auto 100; intuition; cbn in *; simpl in *; auto 100
  | |- context[_] =>
      try contradiction; try discriminate
end.


Inductive action:=
|dummy: action
|start_txn: action
|read_item: version -> action
|write_item: value -> action
|try_commit_txn: action
|lock_write_item: action
|seq_point: action
|validate_read_item: version -> action
|abort_txn: action
|unlock_write_item: action
(*|restart_txn: action*)
|commit_txn: action
|complete_write_item: (*value -> action*)version -> action
(*|unlock_write_item: version -> action*)
(*|invalid_write_item: value -> action*)
|commit_done_txn: action.
(*|obtain_global_tid: action.*)
(*sp later than last lock, but must before the first commit*)
Definition trace := list (tid * action).

(* Return the “phase” of an action. *)
Definition action_phase (a:action) :=
  match a with
  | dummy => 0
  | start_txn => 1
  | read_item _ => 1
  | write_item _ => 1
  | try_commit_txn => 2
  | lock_write_item => 2
  | seq_point => 3
  | validate_read_item _ => 3
  | commit_txn => 4
  | complete_write_item _ => 4
  | commit_done_txn => 4
  | abort_txn => 6
  | unlock_write_item => 6
  end.

Fixpoint trace_tid_phase tid t: nat :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then action_phase a
    else trace_tid_phase tid t'
  | [] => 0
  end.

Fixpoint trace_tid_actions tid t: trace :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then (tid', a) :: (trace_tid_actions tid t')
    else trace_tid_actions tid t'
  | [] => []
  end.

Fixpoint trace_tid_abort tid t: bool :=
  match t with
  | (tid', abort_txn) :: t' => 
    if Nat.eq_dec tid tid'
    then true
    else trace_tid_abort tid t'
  | _ :: t' => trace_tid_abort tid t'
  | [] => false
  end.

(* Return the version number of the last committed write *)
Fixpoint trace_write_version (t:trace): version :=
  match t with
  | (_, complete_write_item v) :: _ => v
  | _ :: t' => trace_write_version t'
  | [] => 0
  end.

Fixpoint trace_tid_last_write tid t: option value :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then match a with
         | write_item v => Some v
         | complete_write_item _ => None
         | _ => trace_tid_last_write tid t'
         end
    else trace_tid_last_write tid t'
  | [] => None
  end.

Fixpoint trace_validate_read tid vers aborted (t:trace) :=
  match t with
  | (tid', lock_write_item) :: t' =>
    (tid = tid' \/ aborted) /\ trace_validate_read tid vers False t'
  | (_, unlock_write_item) :: t' =>
    trace_validate_read tid vers True t'
  | (_, complete_write_item vers') :: _ => vers = vers'
  | _ :: t' => trace_validate_read tid vers aborted t'
  | [] => vers = 0
  end.

Fixpoint locked_by (t:trace) default : tid :=
  match t with
  | (tid, lock_write_item) :: _ => tid
  | (_, unlock_write_item) :: _ => default
  | (_, complete_write_item _) :: _ => default
  | _ :: t' => locked_by t' default
  | [] => default
  end.

Inductive sto_trace : trace -> Prop :=

| empty_step : sto_trace []

| start_txn_step: forall t tid,
    tid > 0
    -> trace_tid_phase tid t = 0
    -> sto_trace t
    -> sto_trace ((tid, start_txn)::t)

| read_item_step: forall t tid,
    trace_tid_phase tid t = 1
    -> locked_by t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, read_item (trace_write_version t)) :: t)

| write_item_step: forall t tid val,
    trace_tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, write_item val) :: t)

| try_commit_txn_step: forall t tid,
    trace_tid_phase tid t = 1
    -> sto_trace t
    -> sto_trace ((tid, try_commit_txn)::t)

| lock_write_item_step: forall t tid v,
    trace_tid_phase tid t = 2
    -> In (tid, write_item v) t
    -> locked_by t 0 = 0
    -> sto_trace t
    -> sto_trace ((tid, lock_write_item) :: t)

(*sequential point*)
| seq_point_step: forall t tid,
    trace_tid_phase tid t = 2
    -> (forall v, In (tid, write_item v) t
                  -> In (tid, lock_write_item) t)
    -> sto_trace t
    -> sto_trace ((tid, seq_point) :: t)

| validate_read_item_step: forall t tid vers,
    trace_tid_phase tid t = 3
    -> locked_by t tid = tid (* unlocked or locked by me *)
    -> trace_write_version t = vers
    -> sto_trace t
    -> sto_trace ((tid, validate_read_item vers) :: t)

| abort_txn_step: forall t tid,
    trace_tid_phase tid t > 0
    -> trace_tid_phase tid t < 4
    -> sto_trace t
    -> sto_trace ((tid, abort_txn) :: t)

| unlock_item_step: forall t tid,
    trace_tid_phase tid t = 6
    -> locked_by t 0 = tid
    -> sto_trace t
    -> sto_trace ((tid, unlock_write_item) :: t)

| commit_txn_step: forall t tid,
    trace_tid_phase tid t = 3
    -> (forall vers, In (tid, read_item vers) t
                     -> In (tid, validate_read_item vers) t)
    -> sto_trace t
    -> sto_trace ((tid, commit_txn) :: t)

| complete_write_item_step: forall t tid val,
    trace_tid_phase tid t = 4
    -> locked_by t 0 = tid
    -> trace_tid_last_write tid t = Some val
    -> sto_trace t
    -> sto_trace ((tid, complete_write_item (S (trace_write_version t))) :: t)

| commit_done_step: forall t tid,
    trace_tid_phase tid t = 4
    -> locked_by t 0 <> tid
    -> sto_trace t
    -> sto_trace ((tid, commit_done_txn) :: t).
Hint Constructors sto_trace.

Definition example_txn:=
[(2, commit_done_txn); (2, complete_write_item 1); (2, commit_txn); (2, validate_read_item 0); (2, seq_point); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (2, read_item 0); (2, start_txn); (1, commit_done_txn); (1, commit_txn); (1, validate_read_item 0); (1, seq_point); (1, try_commit_txn); (1, read_item 0); (1, start_txn)].

Definition example_txn2:=
[(3, commit_done_txn); (3, commit_txn); (3, validate_read_item 1); (3, seq_point); (3, try_commit_txn); (3, read_item 1); (3, start_txn); (1, abort_txn); (1, validate_read_item 1); (1, try_commit_txn); (2, commit_txn); (2, complete_write_item 1); (2, commit_txn); (2, validate_read_item 0); (2, seq_point); (2, lock_write_item); (2, try_commit_txn); (2, write_item 4); (1, read_item 0); (2, read_item 0); (2, start_txn); (1, start_txn)].

(*
Returns the serialized sequence of transactions in the STO trace based on seq_point of each transaction
The first element (tid) of the sequence is the first transaction that completes in the serial trace
Note that STO-trace is constructed in a reverse order: the first (tid * action) pair is the last operation in the trace
*)


Function seq_list (sto_trace: trace): list nat:=
  match sto_trace with
  | [] => []
  | (tid, seq_point) :: tail => tid :: seq_list tail
  | _ :: tail => seq_list tail
  end.

(*
Function seq_list (sl: list nat) (trace : trace) : list nat:=
  match sl with 
  | [] => []
  | hd :: sl' => if trace_tid_abort hd trace
                then seq_list sl' trace
                else hd :: (seq_list sl' trace)
  end.

Eval compute in seq_list_all example_txn.

Eval compute in seq_list_all example_txn2.
*)

(*
Function create_serialized_trace (sto_trace: trace) (sto_trace_copy: trace): trace:=
  match sto_trace with
  | [] => []
  | (tid, seq_point) :: tail
    => (*if trace_tid_abort tid sto_trace (*this tid is aborted*)
       then create_serialized_trace tail sto_trace_copy
       else trace_tid_actions tid sto_trace_copy ++ create_serialized_trace tail sto_trace_copy*)
      trace_tid_actions tid sto_trace_copy 
      ++ create_serialized_trace tail sto_trace_copy
  | _ :: tail => create_serialized_trace tail sto_trace_copy
  end.
*)

Function create_serialized_trace (sto_trace: trace) (seqls : list nat): trace:=
  match seqls with
  | [] => []
  | head :: tail 
    => 
    (*if trace_tid_abort head sto_trace (*this tid is aborted*)
      then create_serialized_trace sto_trace tail
      else trace_tid_actions head sto_trace ++ create_serialized_trace sto_trace tail
    *)
      trace_tid_actions head sto_trace 
      ++ create_serialized_trace sto_trace tail
  end.


(*
The function checks if a trace is a serial trace by making sure that
tid is only increaing as we traverse the trace
In this function, we assume that the trace is in the correct order.
That is, the first (tid*action) in the trace is actually the first one that gets to be executed
*)
Function check_is_serial_trace (tr: trace) : Prop :=
  match tr with 
  | [] => True
  | (tid, x) :: rest =>
    match rest with
    | [] => True
    | (tid', y) :: _ => (tid = tid' \/ trace_tid_actions tid rest = [])
                        /\ check_is_serial_trace rest
    end
  end.

Lemma sto_trace_cons ta t:
  sto_trace (ta :: t) -> sto_trace t.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma sto_trace_app t1 t2:
  sto_trace (t1 ++ t2) -> sto_trace t2.
Proof.
  intros.
  induction t1. rewrite app_nil_l in H. auto.
  apply IHt1.
  now apply sto_trace_cons with (ta:=a).
Qed.

Lemma sto_trace_nil_remove trace :
  sto_trace (trace ++ []) -> sto_trace trace.
Proof.
  intros.
  inversion H. 
  rewrite app_nil_r in H1; now rewrite <- H1.
  1-12: rewrite app_nil_r in H0; rewrite <- H0; auto.
  apply lock_write_item_step with (tid0:= tid0) (v:= v) in H4; auto.
  apply complete_write_item_step with (tid0 := tid0) (val:= val) in H4; auto.
Qed.

Lemma sto_trace_nil_add trace :
  sto_trace (trace) -> sto_trace (trace ++ []).
Proof.
  intros.
  inversion H; subst.
  - simpl; auto.
  - simpl. assert ((tid0, start_txn) :: t = (tid0, start_txn) :: t ++ []).
    apply app_nil_end. rewrite H3 in H. auto.
  - simpl. assert ((tid0, read_item (trace_write_version t)) :: t = (tid0, read_item (trace_write_version t)) :: t ++ []).
    apply app_nil_end. rewrite H3 in H. auto.
  - simpl. assert ((tid0, write_item val) :: t = (tid0, write_item val) :: t ++ []).
    apply app_nil_end. rewrite H2 in H. auto.
  - simpl. assert ((tid0, try_commit_txn) :: t = (tid0, try_commit_txn) :: t ++ []).
    apply app_nil_end. rewrite H2 in H. auto.
  - simpl. assert ((tid0, lock_write_item) :: t = (tid0, lock_write_item) :: t ++ []).
    apply app_nil_end. rewrite H4 in H. auto.
  - simpl. assert ((tid0, seq_point) :: t = (tid0, seq_point) :: t ++ []).
    apply app_nil_end. rewrite H3 in H. auto.
  - simpl. assert ((tid0, validate_read_item (trace_write_version t)) :: t = (tid0, validate_read_item (trace_write_version t)) :: t ++ []).
    apply app_nil_end. rewrite H2 in H. auto.
  - simpl. assert ((tid0, abort_txn) :: t = (tid0, abort_txn) :: t ++ []).
    apply app_nil_end. rewrite H3 in H. auto.
  - simpl. assert ((locked_by t 0, unlock_write_item) :: t = (locked_by t 0, unlock_write_item) :: t ++ []).
    apply app_nil_end. unfold tid in H1. rewrite H1 in H. auto.
  - simpl. assert ((tid0, commit_txn) :: t = (tid0, commit_txn) :: t ++ []).
    apply app_nil_end. rewrite H3 in H. auto.
  - simpl. assert ((locked_by t 0, complete_write_item (S (trace_write_version t))) :: t = (locked_by t 0, complete_write_item (S (trace_write_version t)))
   :: t ++ []).
    apply app_nil_end. unfold tid in H1. rewrite H1 in H. auto.
  - simpl. assert ((tid0, commit_done_txn) :: t = (tid0, commit_done_txn) :: t ++ []).
    apply app_nil_end. rewrite H3 in H. auto.
Qed.

Lemma phase_increase_head tid a t:
  sto_trace ((tid, a) :: t) ->
  action_phase a >= trace_tid_phase tid t.
Proof.
  intros; inversion H; cbn; omega.
Qed.

Lemma phase_increase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_tid_phase tid (t1 ++ t2) >= trace_tid_phase tid t2.
Proof.
  induction t1; intros.
  - simpl; omega.
  - rewrite <- app_comm_cons in H; destruct a.
    assert (sto_trace (t1 ++ t2)) by (now apply sto_trace_cons in H).
    apply IHt1 in H0.
    simpl; destruct (Nat.eq_dec tid t).
    + subst; apply phase_increase_head in H; omega.
    + auto.
Qed.

Lemma phase_increase_in tid a t:
  sto_trace t ->
  In (tid, a) t ->
  trace_tid_phase tid t >= action_phase a.
Proof.
  intros H I; apply in_split in I.
  destruct I as [l1 [l2 L]].
  assert (trace_tid_phase tid ((tid, a) :: l2) = action_phase a). {
    cbn; destruct (Nat.eq_dec tid tid); omega.
  }
  rewrite L in *; rewrite <- H0; now apply phase_increase_app.
Qed.

Lemma phase_increase_in_app tid a (t1 t2:trace):
  sto_trace (t1 ++ t2) ->
  In (tid, a) (t1 ++ t2) ->
  action_phase a > trace_tid_phase tid t2 ->
  In (tid, a) t1.
Proof.
  intros T I A.
  apply in_app_or in I; destruct I as [I | I]; auto.
  apply sto_trace_app in T.
  apply (phase_increase_in _ _ _ T) in I.
  omega.
Qed.
  
Lemma at_most_one_seq_point tid t:
  sto_trace ((tid, seq_point) :: t) ->
  ~ In (tid, seq_point) t.
Proof.
  intros H F.
  apply (phase_increase_in _ _ _ (sto_trace_cons _ _ H)) in F.
  inversion H; subst; cbn in *.
  omega.
Qed.

Lemma at_most_one_seq_point_app t1 t2 tid:
  sto_trace (t1 ++ (tid, seq_point) :: t2)
  -> ~ In (tid, seq_point) t1.
Proof.
  intros H F.
  induction t1; cbn in *; auto.
  destruct F. rewrite H0 in H. 
  inversion H; subst.
  assert (In (tid, seq_point) (t1 ++ (tid, seq_point) :: t2)). {
  apply in_or_app. simpl. right. left. auto. 
  }
  apply phase_increase_in in H0; [ | auto]. rewrite H3 in H0.
  simpl in H0. omega.
  apply sto_trace_cons in H.
  apply IHt1 in H0; auto.
Qed.
    

Lemma trace_phase_in tid t:
  trace_tid_phase tid t > 0 ->
  exists a, In (tid, a) t.
Proof.
  induction t; intros; cbn in *.
  omega.
  destruct a.
  destruct (Nat.eq_dec tid n).
  exists a; subst; now left.
  apply IHt in H; destruct H as [a' H]; exists a'; now right.
Qed.

Lemma tid_nonzero tid a t:
  sto_trace t ->
  In (tid, a) t ->
  tid > 0.
Proof.
  revert tid a; induction t.
  - intros tid a H I; destruct I.
  - intros tid' a' H I.
    destruct I; [ | now apply (IHt _ _ (sto_trace_cons _ _ H)) in H0 ].
    subst; inversion H; auto.
    all: assert (trace_tid_phase tid' t > 0) as GZ by omega.
    all: apply trace_phase_in in GZ.
    all: destruct GZ as [a GZ].
    all: now apply (IHt tid' a).
Qed.

Lemma trace_phase_nonzero tid t:
  sto_trace t ->
  trace_tid_phase tid t > 0 ->
  tid > 0.
Proof.
  intros T; induction T; intros P; simpl in P.
  omega.
  all: destruct (Nat.eq_dec tid tid0); [subst; auto | now apply IHT].
  all: try solve [apply IHT; omega].
Qed.

Lemma trace_lock_cons tid tid' t a:
  sto_trace ((tid', a) :: t) ->
  locked_by t 0 = tid ->
  locked_by ((tid', a) :: t) 0 = tid
  \/ tid = 0 /\ a = lock_write_item
  \/ tid = tid' /\ a = unlock_write_item
  \/ tid = tid' /\ exists val, a = complete_write_item val.
Proof.
  intros T L.
  assert (tid' > 0) as TG. {
    apply tid_nonzero with (a:=a) (t:=(tid', a)::t); cbn; auto.
  }
  inversion T; subst; cbn; auto.
  right; right; right; eauto.
Qed.

Lemma locked_phase tid t:
  sto_trace t ->
  locked_by t 0 = tid ->
  tid > 0 ->
  trace_tid_phase tid t >= 2.
Proof.
  intros T; revert tid; induction T; intros tid L G.
  1: cbn in L; omega.
  all: cbn.
  all: destruct (Nat.eq_dec tid tid0); try omega.
  all: try (now apply IHT).
  1-3: subst; apply IHT in e; omega.
  1-3: simpl in L; omega.
Qed.

Lemma commit_phase_cons tid p t:
  sto_trace (p :: t) ->
  trace_tid_phase tid t = 4 ->
  trace_tid_phase tid (p :: t) = 4.
Proof.
  destruct p as [tid' a]; intros T Fo; inversion T; cbn in *.
  all: destruct (Nat.eq_dec tid tid'); auto.
  all: subst; omega.
Qed.

Lemma commit_phase_app tid t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_tid_phase tid t2 = 4 ->
  trace_tid_phase tid (t1 ++ t2) = 4.
Proof.
  induction t1; intros.
  now simpl.
  rewrite <- app_comm_cons in *.
  apply commit_phase_cons; auto.
  apply IHt1; auto.
  now apply sto_trace_cons in H.
Qed.

Lemma phase_2_preserves_lock tid t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_tid_phase tid (t1 ++ t2) = 2 ->
  locked_by t2 0 = tid ->
  locked_by (t1 ++ t2) 0 = tid.
Proof.
  revert t2.
  induction t1; intros t2 T P L.
  now cbn.
  destruct a as [tid' a].
  cbn in P; destruct (Nat.eq_dec tid tid').
  - destruct a; simpl in *; try omega.
    + rewrite e in *; clear e tid.
      assert (trace_tid_phase tid' t2 >= 2). {
        apply locked_phase.
        now apply sto_trace_app with (t1:=(tid',try_commit_txn)::t1).
        auto.
        apply tid_nonzero with (a:=try_commit_txn) (t:=(tid', try_commit_txn)::t1 ++ t2).
        auto.
        simpl; now left.
      }
      inversion T; subst.
      apply (phase_increase_app (locked_by t2 0)) in H3; omega.
    + auto.
  - assert (locked_by (t1 ++ t2) 0 = tid) as LA. {
      apply IHt1; auto.
      now apply (sto_trace_cons _ _ T).
    }
    clear IHt1 L.

    assert (tid > 0). {
      apply trace_phase_nonzero with (t:=t1++t2).
      now apply sto_trace_cons with (ta:=(tid',a)).
      omega.
    }

    inversion T; cbn in *; auto; omega.
Qed.

Lemma locked_at_commit tid t1 t2 v:
  sto_trace ((tid, seq_point) :: t1 ++ (tid, write_item v) :: t2) ->
  locked_by (t1 ++ (tid, write_item v) :: t2) 0 = tid.
Proof.
  intros T.
  inversion T.
  assert (tid > 0) as TG. {
    apply tid_nonzero with (a:=write_item v) (t:=t); rewrite H0; auto.
    apply in_or_app; right; now left.
  }

  assert (In (tid, lock_write_item) t1). {
    assert (In (tid, lock_write_item) t). {
      rewrite H0.
      apply H2 with (v0:=v).
      apply in_or_app; cbn; intuition.
    }
    apply phase_increase_in_app with (t2:=(tid, write_item v) :: t2); auto.
    now rewrite <- H0.
    simpl; destruct (Nat.eq_dec tid tid); intuition.
  }

  apply in_split in H4.
  destruct H4 as [t1a [t1b T1]].
  subst.
  repeat rewrite <- app_assoc in *.
  repeat rewrite <- app_comm_cons in *.
  remember ((tid, lock_write_item) :: t1b ++ (tid, write_item v) :: t2) as tx.
  assert (locked_by tx 0 = tid). {
    rewrite Heqtx; now cbn.
  }
  assert (trace_tid_phase tid tx = 2). {
    assert (trace_tid_phase tid tx >= 2). {
      apply locked_phase; auto.
      now apply sto_trace_app with (t1:=t1a).
    }
    assert (2 >= trace_tid_phase tid tx). {
      rewrite <- H1.
      now apply phase_increase_app.
    }
    omega.
  }

  apply phase_2_preserves_lock; auto.
Qed.

Lemma action_after_commit t1 t2 tid action:
  sto_trace ((tid, action) :: t1 ++ (tid, commit_txn) :: t2)
  -> action = complete_write_item (S (trace_write_version t2))
     \/ action = commit_done_txn.
Proof.
  intros T.
  assert (trace_tid_phase tid (t1 ++ (tid, commit_txn) :: t2) = 4) as TG4. {
    apply sto_trace_cons in T.
    apply commit_phase_app; auto.
    simpl; destruct (Nat.eq_dec tid tid); congruence.
  }
  inversion T; try omega.
  2: now right.
  left.

  assert (trace_write_version (t1 ++ (tid, commit_txn) :: t2) =
          trace_write_version t2). {
    subst.
    clear TG4 val H2 H3 H4 H5.
    inversion T; subst; clear T H4 val.
    remember (t1 ++ (tid, commit_txn) :: t2) as t.
    clear H0.
    revert t1 t2 tid Heqt H2 H3.
    induction H5; intros t1 t2 tid T P L.
    all: destruct t1; simpl in T.
    1,2: congruence.
    all: inversion T.
    all: cbn in *.
    all: destruct (Nat.eq_dec tid tid0); try congruence.
    1-2,5,7,10,13: rewrite <- H3; apply (IHsto_trace _ _ _ H3); auto.
    1-2: rewrite <- H2; apply (IHsto_trace _ _ _ H2); auto.
    1: rewrite <- H4; apply (IHsto_trace _ _ _ H4); auto.

    assert (tid > 0). {
      apply (trace_phase_nonzero _ _ H5); omega.
    }
    omega.

    rewrite <- H3; apply (IHsto_trace _ _ _ H3); auto.
    rewrite H3; apply commit_phase_app.
    rewrite <- H3; auto.
    cbn; destruct (Nat.eq_dec tid tid); congruence.

    assert (tid > 0). {
      apply (tid_nonzero _ commit_txn _ H5).
      rewrite H4; apply in_or_app; right; now left.
    }
    omega.

    assert (tid > 0). {
      apply (tid_nonzero _ commit_txn _ H5).
      rewrite H4; apply in_or_app; right; now left.
    }
    omega.
  }

  now rewrite H6.
Qed.

Lemma seq_point_to_seq_list t tid:
  In (tid, seq_point) t
  -> In tid (seq_list t).
Proof.
  intros.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; simpl.
  left. auto.
  right. apply IHl. apply in_inv in H. destruct H.
  inversion H. apply Nat.eq_sym in H1. contradiction. auto.
  destruct _x. destruct a.
  all: destruct (Nat.eq_dec tid t); subst; apply IHl; apply in_inv in H; destruct H; try inversion H; auto.
  inversion y.
  contradiction.
Qed.

Lemma seq_list_to_seq_point t tid:
  In tid (seq_list t)
  -> In (tid, seq_point) t.
Proof.
  intros.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; simpl; simpl in H. left. auto.
  destruct H. apply eq_sym in H. congruence. apply IHl in H. right. auto.
  destruct _x. destruct a.
  all: destruct (Nat.eq_dec tid t); subst; apply in_cons; auto.
Qed.

Lemma seq_point_to_seq_list_neg t tid:
  ~ In (tid, seq_point) t
  -> ~ In tid (seq_list t).
Proof.
  intuition.
  now apply seq_list_to_seq_point in H0. 
Qed.

Lemma seq_list_to_seq_point_neg t tid:
  ~ In tid (seq_list t)
  -> ~ In (tid, seq_point) t.
Proof.
  intuition.
  now apply seq_point_to_seq_list in H0.
Qed.

Lemma serial_trace_remove tid action t:
  ~ In tid (seq_list t) -> 
  create_serialized_trace ((tid, action) :: t) (seq_list t)= create_serialized_trace t (seq_list t).
Proof.
  intros NI.
  induction (seq_list t).
  simpl. auto.
  simpl in *.
  assert (a <> tid /\ ~ In tid l). { intuition. }
  destruct H.
  destruct (Nat.eq_dec a tid).
  contradiction.
  apply IHl in H0.
  now rewrite H0.
Qed.

Lemma smaller_than_phase_3_no_seq_point tid t:
  sto_trace t
  -> trace_tid_phase tid t < 3
  -> ~ In (tid, seq_point) t.
Proof.
  intros H T.
  induction H; simpl; auto.

  intuition. inversion H3. simpl in T.
  destruct (Nat.eq_dec tid tid0). subst. 
  assert (trace_tid_phase tid0 t <3). { omega. }
  apply IHsto_trace in H2; [ | auto]. auto.
  apply IHsto_trace in T; [ | auto]. auto.

  intuition. inversion H3. simpl in T.
  destruct (Nat.eq_dec tid tid0). subst. 
  assert (trace_tid_phase tid0 t <3). { omega. }
  apply IHsto_trace in H2; [ | auto]. auto.
  apply IHsto_trace in T; [ | auto]. auto.

  intuition. inversion H2. simpl in T.
  destruct (Nat.eq_dec tid tid0). subst. 
  assert (trace_tid_phase tid0 t <3). { omega. }
  apply IHsto_trace in H2; [ | auto]. auto.
  apply IHsto_trace in T; [ | auto]. auto.

  intuition. inversion H2. simpl in T.
  destruct (Nat.eq_dec tid tid0). subst. 
  assert (trace_tid_phase tid0 t <3). { omega. }
  apply IHsto_trace in H2; [ | auto]. auto.
  apply IHsto_trace in T; [ | auto]. auto.

  intuition. inversion H4. simpl in T.
  destruct (Nat.eq_dec tid tid0). subst. 
  assert (trace_tid_phase tid0 t <3). { omega. }
  apply IHsto_trace in H3; [ | auto]. auto.
  apply IHsto_trace in T; [ | auto]. auto.

  intuition; simpl in T. inversion H3; subst.
  destruct (Nat.eq_dec tid tid). omega. contradiction.
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.

  intuition; simpl in T. inversion H4; subst. 
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.

  intuition; simpl in T. inversion H3; subst. 
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.

  intuition; simpl in T. inversion H3; subst. 
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.

  intuition; simpl in T. inversion H3; subst. 
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.

  intuition; simpl in T. inversion H4; subst. 
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.

  intuition; simpl in T. inversion H3; subst. 
  destruct (Nat.eq_dec tid tid0). omega. now apply IHsto_trace in T.
Qed.

Lemma serial_trace_remove_before_seq_point tid action t:
  sto_trace ((tid, action) :: t) ->
  trace_tid_phase tid ((tid, action) :: t) < 3
  -> create_serialized_trace ((tid, action) :: t) (seq_list ((tid, action) :: t)) = 
     create_serialized_trace t (seq_list t).
Proof.
  intros H P.
  inversion H; subst.

  simpl. apply smaller_than_phase_3_no_seq_point in P; [ | auto]. simpl in P.
  assert ((tid, start_txn) <> (tid, seq_point) /\ ~In (tid, seq_point) t). { intuition. } destruct H0.
  apply seq_point_to_seq_list_neg in H1.
  now apply serial_trace_remove with (action0 := start_txn) in H1.

  simpl. apply smaller_than_phase_3_no_seq_point in P; [ | auto]. simpl in P.
  assert ((tid, read_item (trace_write_version t)) <> (tid, seq_point) /\ ~In (tid, seq_point) t). { intuition. } destruct H0.
  apply seq_point_to_seq_list_neg in H1.
  now apply serial_trace_remove with (action0 := read_item (trace_write_version t)) in H1.

  simpl. apply smaller_than_phase_3_no_seq_point in P; [ | auto]. simpl in P.
  assert ((tid, write_item val) <> (tid, seq_point) /\ ~In (tid, seq_point) t). { intuition. } destruct H0.
  apply seq_point_to_seq_list_neg in H1.
  now apply serial_trace_remove with (action0 := write_item val) in H1.
 
  simpl. apply smaller_than_phase_3_no_seq_point in P; [ | auto]. simpl in P.
  assert ((tid, try_commit_txn) <> (tid, seq_point) /\ ~In (tid, seq_point) t). { intuition. } destruct H0.
  apply seq_point_to_seq_list_neg in H1.
  now apply serial_trace_remove with (action0 := try_commit_txn) in H1.
   
  simpl. apply smaller_than_phase_3_no_seq_point in P; [ | auto]. simpl in P.
  assert ((tid, lock_write_item) <> (tid, seq_point) /\ ~In (tid, seq_point) t). { intuition. } destruct H0.
  apply seq_point_to_seq_list_neg in H1.
  now apply serial_trace_remove with (action0 := lock_write_item) in H1.

  all: simpl in P; try destruct (Nat.eq_dec tid tid); try omega; try contradiction.
  all: destruct (Nat.eq_dec (locked_by t 0) (locked_by t 0)); try omega; try contradiction.
Qed.

Lemma tid_filter_same_phase tid trace:
  trace_tid_phase tid trace = trace_tid_phase tid (trace_tid_actions tid trace).
Proof.
  induction trace; simpl; auto.
  destruct a.
  destruct (Nat.eq_dec tid n).
  subst. simpl.
  destruct (Nat.eq_dec n n).
  subst. auto. contradiction. auto.
Qed.

Lemma tid_filter_in tid a t:
  In (tid, a) t
  -> In (tid, a) (trace_tid_actions tid t).
Proof.
  intros.
  induction t. simpl. auto.
  destruct a0. simpl in *. destruct H. inversion H; subst.
  all: destruct (Nat.eq_dec tid tid).
  all: simpl; auto; try contradiction.
  destruct (Nat.eq_dec tid n).
  apply IHt in H. simpl. right. auto. auto.
Qed.

Lemma tid_filter_in_rev tid a t:
  In (tid, a) (trace_tid_actions tid t)
  -> In (tid, a) t.
Proof.
  intros.
  induction t. simpl. auto.
  destruct a0. simpl in *.
  destruct (Nat.eq_dec tid n). subst.
  simpl in H. destruct H. now left.
  all: right; auto.
Qed.

Lemma tid_filter_in_iff tid a t:
  In (tid, a) t
  <-> In (tid, a) (trace_tid_actions tid t).
Proof.
  split.
  apply tid_filter_in.
  apply tid_filter_in_rev.
Qed.

(*
Lemma tid_filter_locked_by tid t:
sto_trace t
-> locked_by t tid = tid 
-> locked_by (trace_tid_actions tid t) tid = tid.
Proof.
  intros.
  induction H; simpl. auto.
  all: destruct (Nat.eq_dec tid tid0); subst.
  all: simpl in *; auto.
  apply eq_sym in H0. contradiction.

  simpl in H.
  destruct a. auto. auto. auto. auto. auto.
  apply eq_sym in H. contradiction.
  auto. auto. auto.
  admit.
  unfold locked_by in *.
Admitted.
*)
Lemma NotIn_split (tid: nat) (ls: list nat) (first: nat):
  ~ In tid (ls ++ [first]) ->
  ~ In tid ls /\ (first <> tid).
Proof.
  intros.
  intuition.
  subst.
  assert (In tid (ls ++ [tid])). {
  apply in_or_app. right. simpl. auto.
  }
  apply H in H0. auto.
Qed.

Lemma is_sto_trace_start t s1 first:
   sto_trace t ->
   seq_list t = s1 ++ [first] ->
   sto_trace (create_serialized_trace t [first]).
Proof.
  intros; simpl.
  induction H; simpl. auto.
  
  1-5:  assert (trace_tid_phase tid0 t < 3) as GT3; try omega.
  1-5:  apply smaller_than_phase_3_no_seq_point in GT3; [ | auto].
  1-5:  apply seq_point_to_seq_list_neg in GT3; simpl in H0; rewrite H0 in GT3; apply NotIn_split in GT3; destruct GT3.
  all: destruct (Nat.eq_dec first tid0); try contradiction. 
  1-5: apply IHsto_trace in H0; auto.

  all: simpl in H0; try apply IHsto_trace in H0; auto.    
  all: rewrite tid_filter_same_phase in H.
  apply sto_trace_nil_add.
  assert (forall v : value,
     In (tid0, write_item v) (trace_tid_actions tid0 t) -> In (tid0, lock_write_item) (trace_tid_actions tid0 t)).
  { intros. apply tid_filter_in_rev in H3. apply H1 in H3. apply tid_filter_in. auto. }
  admit. admit.
  
  
  




Admitted.

Lemma seq_list_empty t tid:
sto_trace t
-> seq_list t = []
-> sto_trace (trace_tid_actions tid t).


Lemma commit_in_phase4 tid t:
  sto_trace t ->
  trace_tid_phase tid t = 4 ->
  In (tid, commit_txn) t.
Proof.
  intros S T.
  induction t; simpl. inversion T.
  destruct a. simpl in T. destruct (Nat.eq_dec tid t0).
  destruct a; simpl. 
  all: try inversion T.
  left. rewrite e. auto.
  inversion S.
  rewrite <- e in H2.
  apply IHt in H2. right. auto.
  auto.
  
  inversion S.
  rewrite <- e in H1.
  apply IHt in H1. right. auto.
  auto.
  
  apply IHt in T.
  apply IHt in H0. right. auto.
  apply sto_trace_cons in S.
  auto.
  apply sto_trace_cons in S.
  auto.
Qed.

Lemma seq_point_in_phase3 tid t:
  sto_trace t ->
  trace_tid_phase tid t = 3 ->
  In (tid, seq_point) t.
Proof.
  intros.
  induction t.
  inversion H0.
  destruct a; simpl in *.
  destruct (Nat.eq_dec tid t0). subst.
  destruct a; try inversion H0.
  now left.
  inversion H. apply IHt in H4; [auto | auto].
  apply IHt in H0; [auto| auto].
  apply sto_trace_cons in H; auto.
Qed.

Lemma seq_point_in_commit_head tid t:
  sto_trace ((tid, commit_txn) :: t) ->
  In (tid, seq_point) t.
Proof.
  intros.
  inversion H.
  apply seq_point_in_phase3 in H2; auto.
Qed.

Lemma seq_point_in_commit_in tid t1 t2:
  sto_trace (t1 ++ (tid, commit_txn) :: t2) ->
  In (tid, seq_point) t2.
Proof.
  intros.
  apply seq_point_in_commit_head.
  apply sto_trace_app with (t1 := t1); auto.
Qed.

(*
Lemma in_seq_list_subset tid t c1 c2:
  In tid (seq_list' t c2) ->
  (forall x, In x c2 -> In x c1) ->
  In tid (seq_list' t c1).
*)

(* this is assuming a definition of seq_list' that works correctly for the correct defn of seq_point *)

Lemma seq_list_split t1 t2:
  seq_list (t1 ++ t2) = seq_list t1 ++ seq_list t2.
Proof.
  intros.
  induction t1.
  simpl. auto.
  simpl in *. destruct a. destruct a.
  all: simpl in *; auto.
  rewrite IHt1. auto.
Qed.

Lemma commit_seq_point_in_seq_list tid (t1 t2 t3:trace):
  In tid (seq_list (t1 ++ (tid, commit_txn) :: t2 ++ (tid, seq_point) :: t3)).
Proof.
  rewrite seq_list_split; apply in_or_app; right.
  simpl. rewrite seq_list_split; apply in_or_app; right.
  simpl. left. auto.
Qed.

Lemma in_seq_list_iff tid t:
  sto_trace t ->
  trace_tid_phase tid t = 4 -> In tid (seq_list t).
Proof.
  intros.
  apply commit_in_phase4 in H0; [ | auto].
  apply in_split in H0.
  destruct H0. destruct H0.
  rewrite H0 in *.
  apply sto_trace_app in H.
  inversion H.
  apply seq_point_in_phase3 in H3. apply seq_point_to_seq_list in H3. 
  rewrite seq_list_split. apply in_or_app. simpl. now right. auto.
  
  (********************************************)
(*our seq_list definition contains abort, so this lemma is not iff...*)
Qed.

(*
Lemma is_sto_trace_filter_tid tid t:
  sto_trace t 
  -> sto_trace (trace_tid_actions tid t).
Proof.
  intros S. 
  induction S; simpl; auto.
  all: destruct (Nat.eq_dec tid tid0); subst.
  all: auto.

  rewrite tid_filter_same_phase in H0. 
  apply start_txn_step with (tid:= tid0) in IHS; auto. auto.

  rewrite tid_filter_same_phase in H.
  apply tid_filter_locked_by with (tid0:= tid0) in H0.
  apply read_item_step with (tid0:= tid0) in IHS; auto.

  destruct (Nat.eq_dec tid tid0); subst.
admit. auto.
  admit.
  destruct (Nat.eq_dec tid tid0); subst.
  rewrite tid_filter_same_phase in H.
  apply try_commit_txn_step with (tid:= tid0) in IHS; auto. auto.
  destruct (Nat.eq_dec tid tid0); subst.

  apply start_txn_step with (tid:= tid0) in IHsto_trace; auto.
Admitted.
*)
Lemma is_sto_trace trace:
  sto_trace trace ->
  sto_trace (create_serialized_trace trace (seq_list trace)).
Proof.
  intros H.
  assert (sto_trace trace). { auto. }
  induction H; simpl; auto; try apply IHsto_trace in H2.

  assert (trace_tid_phase tid0 ((tid0, start_txn) :: t) < 3). { 
  simpl. destruct (Nat.eq_dec tid0 tid0). omega. contradiction. }
  apply serial_trace_remove_before_seq_point in H3.
  simpl in H3. unfold tid in H3. rewrite H3. auto. auto.

  assert (trace_tid_phase tid0 ((tid0, read_item (trace_write_version t)) :: t) < 3). { 
  simpl. destruct (Nat.eq_dec tid0 tid0). omega. contradiction. }
  apply serial_trace_remove_before_seq_point in H3.
  simpl in H3. unfold tid in H3. rewrite H3. auto. auto.

  assert (trace_tid_phase tid0 ((tid0, write_item val) :: t) < 3). { 
  simpl. destruct (Nat.eq_dec tid0 tid0). omega. contradiction. }
  apply serial_trace_remove_before_seq_point in H2.
  simpl in H2. unfold tid in H2. rewrite H2. auto. auto.

  assert (trace_tid_phase tid0 ((tid0, try_commit_txn) :: t) < 3). { 
  simpl. destruct (Nat.eq_dec tid0 tid0). omega. contradiction. }
  apply serial_trace_remove_before_seq_point in H2.
  simpl in H2. unfold tid in H2. rewrite H2. auto. auto.

  assert (trace_tid_phase tid0 ((tid0, lock_write_item) :: t) < 3). { 
  simpl. destruct (Nat.eq_dec tid0 tid0). omega. contradiction. }
  apply serial_trace_remove_before_seq_point in H4.
  simpl in H4. unfold tid in H4. rewrite H4. auto. auto.

  destruct (Nat.eq_dec tid0 tid0).
  admit. contradiction.
Admitted.

Fixpoint trace_filter_abort tid t: trace :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then trace_filter_abort tid t'
    else (tid', a) :: (trace_filter_abort tid t')
  | [] => []
  end.

Function filter_sto_trace (sto_trace: trace): trace:=
  match sto_trace with
  | (tid, unlock_write_item) :: tail => trace_filter_abort tid (filter_sto_trace tail)
  | (tid, abort_txn) :: tail => trace_filter_abort tid (filter_sto_trace tail)
  | _ :: tail => filter_sto_trace tail
  | [] => []
  end.

Lemma no_abort_trace_same_as_before tr:
  sto_trace tr
  -> sto_trace (filter_sto_trace tr).
Proof.
  intros.
  induction H; simpl; auto.
  assert (sto_trace ((tid0, abort_txn)::t)). { apply abort_txn_step with (tid:= tid0) in H1; auto. }
  
  induction (filter_sto_trace t).
  simpl; auto.
  destruct a. simpl. destruct (Nat.eq_dec tid0 t1); subst.
  apply sto_trace_cons in IHsto_trace. auto.
  inversion IHsto_trace; subst.
admit.


Function swap_actions (tr: trace) : trace :=
  match tr with
  | () :: () :: tail => 











