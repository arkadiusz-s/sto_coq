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
|start_txn: action
|read_item: version -> action
|write_item: value -> action
|try_commit_txn: action
|lock_write_item: action
|seq_point: action
|validate_read_item: version -> action
|abort_txn: action
|unlock_write_item: action
|commit_txn: action
|complete_write_item: version -> action
|commit_done_txn: action.
Definition trace := list (tid * action).
Definition ta := (tid, action).

(* Return the “phase” of an action. *)
Definition action_phase (a:action) :=
  match a with
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

Fixpoint trace_tid_abort tid t: bool :=
  match t with
  | (tid', abort_txn) :: t' => 
    if Nat.eq_dec tid tid'
    then true
    else trace_tid_abort tid t'
  | _ :: t' => trace_tid_abort tid t'
  | [] => false
  end.


Fixpoint trace_tid_actions tid t: trace :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then (tid', a) :: (trace_tid_actions tid t')
    else trace_tid_actions tid t'
  | [] => []
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

Definition tid_in_phase_4 (tid: tid) (t: trace): Prop:=
  trace_tid_phase tid t = 4.

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
    -> (forall vers, In (tid, validate_read_item vers) t
                     -> In (tid, read_item vers) t)
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

Inductive committed_unconflicted_sto_trace : trace -> Prop :=
| construct_cust: forall tr,
  sto_trace tr
  -> (forall tid, trace_tid_phase tid tr > 0 -> trace_tid_phase tid tr = 4)
  -> committed_unconflicted_sto_trace tr.
Hint Constructors committed_unconflicted_sto_trace.

Definition is_not_seq_point (a:action) : bool :=
  match a with
  | seq_point => false
  | _ => true
  end.

Function seq_list (sto_trace: trace): list nat:=
  match sto_trace with
  | [] => []
  | (tid, seq_point) :: tail => tid :: seq_list tail
  | _ :: tail => seq_list tail
  end.

Function tid_list (sto_trace: trace): list nat:=
  match sto_trace with
  | [] => []
  | (tid, start_txn) :: tail => tid :: tid_list tail
  | _ :: tail => tid_list tail
  end.

Fixpoint In_bool (a:nat) (l:list nat) : bool :=
  match l with
    | [] => false
    | b :: m => (b =? a) || In_bool a m
  end.

Function swap1 t tid: trace :=
  match t with 
  | (tid1, a1) :: tail =>
    match tail with
    | (tid2, a2) :: tail' =>
    if Nat.eq_dec tid1 tid2 
        then (tid1, a1) :: (swap1 tail tid)
      else if (tid =? tid1) && (3 <=? action_phase a1) && (is_not_seq_point a1)
        then (tid2, a2)::(tid1, a1)::tail'
      else if (tid =? tid2) && (action_phase a2 <? 3)
        then (tid2, a2)::(tid1, a1)::tail'
      else (tid1, a1) :: (swap1 tail tid)
    | [] => [(tid1,a1)]
    end
  | [] => []
  end.

Function swaps t tid num: trace:=
  match num with
  | 0 => t
  | S n => swaps (swap1 t tid) tid n
  end.

Function create_serialized_trace (t: trace) (sl : list nat):=
  match sl with
  | head :: tail => create_serialized_trace (swaps t head ((length t) * (length t))) tail
  | [] => t
  end.

(******************************************)
Theorem cust_is_sto_trace t:
  committed_unconflicted_sto_trace t
  -> sto_trace t.
Proof.
  intros CUST; induction CUST; simpl; auto.
Qed.
(******************************************)

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

Lemma swap1_not_change_phase t tid tid0:
  trace_tid_phase tid t = trace_tid_phase tid (swap1 t tid0).
Proof.
  functional induction (swap1 t tid0).
  simpl in *. destruct (Nat.eq_dec tid tid1); auto.
  simpl.
  destruct (Nat.eq_dec tid tid1).
  destruct (Nat.eq_dec tid tid2).
  clear e1.
  rewrite <- e in _x. rewrite <- e0 in _x. contradiction. auto.
  destruct (Nat.eq_dec tid tid2). auto. auto.
  simpl.
  destruct (Nat.eq_dec tid tid1).
  destruct (Nat.eq_dec tid tid2).
  clear e1.
  rewrite <- e in _x. rewrite <- e0 in _x. contradiction. auto.
  destruct (Nat.eq_dec tid tid2). auto. auto.
  simpl in *. 
  destruct (Nat.eq_dec tid tid2); auto; destruct (Nat.eq_dec tid tid1); auto.
  auto. auto.
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

Lemma trace_phase_in_tid_list tid t:
  sto_trace t
  -> trace_tid_phase tid t > 0 ->
  In tid (tid_list t).
Proof.
  intros.
  induction H; cbn in *.
  omega.
  all: destruct (Nat.eq_dec tid tid0); try rewrite e in *; simpl; auto.
  all: try assert (trace_tid_phase tid0 t > 0); try rewrite H; try omega; try apply IHsto_trace; auto.
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

Lemma swap1_not_change_lock t tid tid0:
  sto_trace t -> 
  locked_by t tid = locked_by (swap1 t tid0) tid.
Proof.
  intros ST.
  functional induction (swap1 t tid0).
  assert (sto_trace ((tid1, a1) :: (tid1, a2) :: tail')). auto.
  apply sto_trace_cons in H. apply IHt0 in H.
  simpl.
  destruct a1; subst; simpl in *; auto.
  assert ((3 <=? action_phase a1) = true).
  apply andb_true_iff in e2.
  destruct e2.
  apply andb_true_iff in H.
  destruct H.
  auto.
  assert (a1 <> lock_write_item).
  apply leb_complete in H. destruct a1; intuition; inversion H0. simpl in H. omega.
  simpl. destruct a1; auto. intuition.
  destruct a2; auto.
  inversion ST. simpl in H4. clear e1. rewrite H4 in _x. contradiction.
  destruct a2; auto.
  inversion ST. simpl in H5. clear e1. rewrite H5 in _x. contradiction.
  apply andb_true_iff in e3. destruct e3.
  apply Nat.ltb_lt in H0.
  simpl. destruct a2; auto.
  destruct a1; auto.
  inversion ST. simpl in H5.
  assert (In (tid2, lock_write_item) ((tid2, lock_write_item) :: tail')). simpl. auto.
  apply tid_nonzero in H7; auto. rewrite H5 in H7. omega.
  inversion ST. simpl in H4. clear e1. rewrite H4 in _x. contradiction.
  inversion ST. simpl in H5. clear e1. rewrite H5 in _x. contradiction.
  simpl in H0; omega. simpl in H0; omega.
  apply sto_trace_cons in ST. apply IHt0 in ST.
  simpl. 
  destruct a1; auto.
  auto. auto.
Qed.
  
Lemma swap1_not_change_write_version t tid:
  sto_trace t
  -> trace_write_version t = trace_write_version (swap1 t tid).
Proof.
  intros ST.
  functional induction (swap1 t tid).
  apply sto_trace_cons in ST. apply IHt0 in ST.
  simpl in *; destruct a1; auto.
  apply andb_true_iff in e2.
  destruct e2.
  apply andb_true_iff in H.
  destruct H.
  apply leb_complete in H1.
  simpl. destruct a1; auto.
  destruct a2; auto.
  inversion ST. simpl in H6.
  assert (In (tid1, complete_write_item v) ((tid1, complete_write_item v) :: (tid2, complete_write_item v0) :: tail')). simpl. auto.
  apply tid_nonzero in H9; auto. rewrite H6 in H9. omega.
  apply andb_true_iff in e3. 
  destruct e3.
  apply Nat.ltb_lt in H0.
  simpl. destruct a1; auto.
  destruct a2; auto.
  simpl in H0. omega.
  apply sto_trace_cons in ST. apply IHt0 in ST.
  simpl in *; destruct a1; auto.
  auto. auto.
Qed.

Lemma swap1_not_change_in tid action t tid0:
  In (tid, action) t -> In (tid, action) (swap1 t tid0).
Proof.
  intros.
  functional induction (swap1 t tid0).
  simpl in H. destruct H. simpl. auto.
  simpl in IHt0. apply IHt0 in H. simpl. auto.
  simpl in *. destruct H. auto. destruct H. auto. auto.
  simpl in *. destruct H. auto. destruct H. auto. auto.
  simpl in H. destruct H. simpl. auto.
  simpl in IHt0. apply IHt0 in H. simpl. auto.
  auto. auto.
Qed.

Lemma swap1_not_change_in_rev tid action t tid0:
  In (tid, action) (swap1 t tid0) -> In (tid, action) t.
Proof.
  intros.
  functional induction (swap1 t tid0).
  simpl in H. destruct H. simpl. auto.
  simpl in IHt0. apply IHt0 in H. simpl. auto.
  simpl in *. destruct H. auto. destruct H. auto. auto.
  simpl in *. destruct H. auto. destruct H. auto. auto.
  simpl in H. destruct H. simpl. auto.
  simpl in IHt0. apply IHt0 in H. simpl. auto.
  auto. auto.
Qed.

Lemma swap1_not_change_last_write tid tid0 t:
  sto_trace t
  -> trace_tid_last_write tid t = trace_tid_last_write tid (swap1 t tid0).
Proof.
  intros ST.
  functional induction (swap1 t tid0).
  apply sto_trace_cons in ST; apply IHt0 in ST.
  simpl in *. destruct (Nat.eq_dec tid tid1); subst.
  destruct a1; auto. auto.
  simpl.
  destruct (Nat.eq_dec tid tid1).
  destruct a1; auto.
  destruct a2; auto.
  clear e1. rewrite <- e in _x.
  1-12: destruct (Nat.eq_dec tid tid2); try contradiction; auto.
  1-2: clear e1; rewrite <- e in _x; rewrite <- e0 in _x; contradiction.
  destruct a2; auto.
  1-12: destruct (Nat.eq_dec tid tid2); try contradiction; auto.
  clear e1; rewrite <- e in _x; rewrite <- e0 in _x; contradiction.
  destruct a2; auto.
  simpl.
  destruct (Nat.eq_dec tid tid1).
  destruct a1; auto.
  destruct a2; auto.
  clear e1. rewrite <- e in _x.
  1-12: destruct (Nat.eq_dec tid tid2); try contradiction; auto.
  1-2: clear e1; rewrite <- e in _x; rewrite <- e0 in _x; contradiction.
  destruct a2; auto.
  1-12: destruct (Nat.eq_dec tid tid2); try contradiction; auto.
  clear e1; rewrite <- e in _x; rewrite <- e0 in _x; contradiction.
  destruct a2; auto.
  apply sto_trace_cons in ST; apply IHt0 in ST.
  simpl in *. destruct (Nat.eq_dec tid tid1); subst.
  destruct a1; auto. auto.
  auto. auto.
Qed.

Lemma swap_not_change_phase t t' tid0 tid1 tid2 a1 a2:
  tid1 <> tid2
  -> trace_tid_phase tid0 (t' ++ (tid1, a1) :: (tid2, a2) :: t) = trace_tid_phase tid0 (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Proof.
  intros.
  induction t'; simpl; auto.
  destruct (Nat.eq_dec tid0 tid1); simpl; auto.
  destruct (Nat.eq_dec tid0 tid2); simpl; auto.
  rewrite <- e in H. rewrite <- e0 in H. contradiction.
  destruct a.
  destruct (Nat.eq_dec tid0 n); auto.
Qed.

Lemma swap_not_change_lock0 t t' a1 a2 tid1 tid2:
  sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> tid1 <> tid2
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> 3 <= action_phase a1
  -> a1 <> seq_point
  -> locked_by (t' ++ (tid1, a1) :: (tid2, a2) :: t) 0 = locked_by (t' ++ (tid2, a2) :: (tid1, a1) :: t) 0.
Proof.
  intros ST NE AP1 AP2 GT3 NSP.
  induction t'. simpl. destruct a1; auto.
  destruct a2; auto. simpl in ST. inversion ST. simpl in H3.
  assert (In (tid2, lock_write_item) ((tid1, lock_write_item) :: (tid2, lock_write_item) :: t)). simpl; auto. apply tid_nonzero in H5; auto. rewrite H3 in H5. omega.
  simpl in *. omega. simpl in *. omega.
  all: simpl in *; try omega.
  destruct a2; auto. inversion ST. simpl in H3. rewrite H3 in NE; try contradiction.
  destruct a. destruct a; apply sto_trace_cons in ST; auto.
Qed.

Lemma swap_not_change_lock0_2 t t' a1 a2 tid1 tid2:
  sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> tid1 <> tid2
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> action_phase a2 < 3
  -> locked_by (t' ++ (tid1, a1) :: (tid2, a2) :: t) 0 = locked_by (t' ++ (tid2, a2) :: (tid1, a1) :: t) 0.
Proof.
  intros ST NE AP1 AP2 LT3.
  induction t'. simpl. destruct a1; auto.
  destruct a2; auto. simpl in ST. inversion ST. simpl in H3.
  assert (In (tid2, lock_write_item) ((tid1, lock_write_item) :: (tid2, lock_write_item) :: t)). simpl; auto. apply tid_nonzero in H5; auto. rewrite H3 in H5. omega.
  simpl in *. omega. simpl in *. omega.
  all: simpl in *; try omega.
  destruct a2; auto. inversion ST. simpl in H3. rewrite H3 in NE; try contradiction.
  destruct a. destruct a; apply sto_trace_cons in ST; auto.
Qed.

Lemma swap_not_change_lock0' t t' a1 a2 tid1 tid2 tid:
  sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> tid1 <> tid2
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> 3 <= action_phase a1
  -> a1 <> seq_point
  -> locked_by (t' ++ (tid1, a1) :: (tid2, a2) :: t) tid = locked_by (t' ++ (tid2, a2) :: (tid1, a1) :: t) tid.
Proof.
  intros ST NE AP1 AP2 GT3 NSP.
  induction t'. simpl. destruct a1; auto.
  destruct a2; auto. simpl in ST. inversion ST. simpl in H3.
  assert (In (tid2, lock_write_item) ((tid1, lock_write_item) :: (tid2, lock_write_item) :: t)). simpl; auto. apply tid_nonzero in H5; auto. rewrite H3 in H5. omega.
  simpl in *. omega. simpl in *. omega.
  all: simpl in *; try omega.
  destruct a2; auto. inversion ST. simpl in H3. rewrite H3 in NE; try contradiction.
  destruct a. destruct a; apply sto_trace_cons in ST; auto.
Qed.

Lemma swap_not_change_lock0_2' t t' a1 a2 tid1 tid2 tid:
  sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> tid1 <> tid2
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> action_phase a2 < 3
  -> locked_by (t' ++ (tid1, a1) :: (tid2, a2) :: t) tid = locked_by (t' ++ (tid2, a2) :: (tid1, a1) :: t) tid.
Proof.
  intros ST NE AP1 AP2 LT3.
  induction t'. simpl. destruct a1; auto.
  destruct a2; auto. simpl in ST. inversion ST. simpl in H3.
  assert (In (tid2, lock_write_item) ((tid1, lock_write_item) :: (tid2, lock_write_item) :: t)). simpl; auto. apply tid_nonzero in H5; auto. rewrite H3 in H5. omega.
  simpl in *. omega. simpl in *. omega.
  all: simpl in *; try omega.
  destruct a2; auto. inversion ST. simpl in H3. rewrite H3 in NE; try contradiction.
  destruct a. destruct a; apply sto_trace_cons in ST; auto.
Qed.

Lemma swap_not_change_write_version t t' tid1 tid2 a1 a2:
  tid1 <> tid2
  -> sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> trace_write_version (t' ++ (tid1, a1) :: (tid2, a2) :: t) = trace_write_version (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Proof.
  intros NE ST.
  induction t'. simpl in *. destruct a1; auto.
  destruct a2; auto.
  inversion ST. simpl in H3.
  assert (In (tid1, complete_write_item v) ((tid1, complete_write_item v) :: (tid2, complete_write_item v0) :: t)). simpl; auto. apply tid_nonzero in H6; auto. rewrite <- H3 in H6. omega.
  simpl.
  destruct a. destruct a; apply sto_trace_cons in ST; auto.
Qed.

Lemma swap_not_change_in t t' (tid1 tid2 tid: tid) (a1 a2 action: action):
  tid1 <> tid2
  -> In (tid, action) (t' ++ (tid1, a1) :: (tid2, a2) :: t) 
  -> In (tid, action) (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Proof.
  intros NE IN.
  apply in_or_app. apply in_app_or in IN.
  simpl in *.
  destruct IN; auto.
  destruct H; auto.
  destruct H; auto.
Qed.

Lemma swap_not_change_in_rev t t' (tid1 tid2 tid: tid) (a1 a2 action: action):
  tid1 <> tid2
  -> In (tid, action) (t' ++ (tid2, a2) :: (tid1, a1) :: t) -> In (tid, action) (t' ++ (tid1, a1) :: (tid2, a2) :: t).
Proof.
  intros NE IN.
  apply in_or_app. apply in_app_or in IN.
  simpl in *.
  destruct IN; auto.
  destruct H; auto.
  destruct H; auto.
Qed.

Lemma swap_not_change_last_write t t' tid1 tid2 tid a1 a2:
  tid1 <> tid2
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> trace_tid_last_write tid (t' ++ (tid1, a1) :: (tid2, a2) :: t) = trace_tid_last_write tid (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Proof.
  intros NE AP1 AP2 ST.
  induction t'. simpl in *.
  destruct (Nat.eq_dec tid tid1).
  destruct a1; destruct (Nat.eq_dec tid tid2); try rewrite <- e in NE; try rewrite <- e0 in NE; try contradiction; auto.
  destruct (Nat.eq_dec tid tid2); auto.
  simpl in *. destruct a.
  destruct (Nat.eq_dec tid t0).
  destruct a; apply sto_trace_cons in ST; auto.
  apply sto_trace_cons in ST; auto.
Qed.


Lemma sto_trace_swap_app tid1 tid2 a1 a2 t t':
  sto_trace ((tid2, a2) :: (tid1, a1) :: t)
  -> sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> 3 <= action_phase a1
  -> a1 <> seq_point
  -> tid1 <> tid2
  -> sto_trace (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Proof.
  intros ST ST2 AP AP2 AP3 SQ NE.
  induction t'.
  simpl;auto.
  destruct a. simpl in ST2.
  induction a; inversion ST2.

  apply IHt' in H3.
  rewrite swap_not_change_phase in H2.
  apply start_txn_step with (tid:=t0) in H3; auto. auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H4. simpl.
  rewrite swap_not_change_phase in H2; auto.
  rewrite swap_not_change_lock0 in H3; auto.
  rewrite swap_not_change_write_version; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3. simpl.
  rewrite swap_not_change_phase in H1; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H2. simpl.
  rewrite swap_not_change_phase in H1; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H4. simpl.
  rewrite swap_not_change_phase in H1; auto.
  apply swap_not_change_in in H2; auto.
  rewrite swap_not_change_lock0 in H3; auto.
  apply lock_write_item_step with (tid0:= t0) (v:=v) in H4; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3. simpl.
  rewrite swap_not_change_phase in H1; auto.
  assert (forall v : value,
     In (t0, write_item v) (t' ++ (tid2, a2) :: (tid1, a1) :: t) ->
     In (t0, lock_write_item) (t' ++ (tid2, a2) :: (tid1, a1) :: t)).
  intros. apply swap_not_change_in_rev in H4; auto. apply H2 in H4. apply swap_not_change_in in H4; auto.
  apply seq_point_step with (tid:= t0) in H3; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H5. simpl.
  rewrite swap_not_change_phase in H2; auto.
  rewrite swap_not_change_lock0' in H3; auto.
  rewrite swap_not_change_write_version in H4; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3	. simpl.
  rewrite swap_not_change_phase in H1; auto.
  rewrite swap_not_change_phase in H2; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3	. simpl.
  rewrite swap_not_change_phase in H1; auto.
  rewrite swap_not_change_lock0' in H2; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H4. simpl.
  rewrite swap_not_change_phase in H1; auto.
  assert (forall vers : version,
     In (t0, read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t) ->
     In (t0, validate_read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t)).
  intros. apply swap_not_change_in_rev in H5; auto. apply H2 in H5. apply swap_not_change_in in H5; auto.
  assert (forall vers : version,
     In (t0, validate_read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t) ->
     In (t0, read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t)).
  intros. apply swap_not_change_in_rev in H6; auto. apply H3 in H6. apply swap_not_change_in in H6; auto.
  apply commit_txn_step with (tid:= t0) in H4; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H5. simpl.
  rewrite swap_not_change_phase in H2; auto.
  rewrite swap_not_change_lock0' in H3; auto.
  rewrite swap_not_change_last_write in H4; auto.
  rewrite swap_not_change_write_version; auto.
  apply complete_write_item_step with (tid0:= t0) (val:= val) in H5; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3	. simpl.
  rewrite swap_not_change_phase in H1; auto.
  rewrite swap_not_change_lock0' in H2; auto.
Qed.

Lemma sto_trace_swap_app2 tid1 tid2 a1 a2 t t':
  sto_trace ((tid2, a2) :: (tid1, a1) :: t)
  -> sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> action_phase a2 < 3
  -> tid1 <> tid2
  -> sto_trace (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Proof.
  intros ST ST2 AP AP2 LT3 NE.
  induction t'.
  simpl;auto.
  destruct a. simpl in ST2.
  induction a; inversion ST2.

  apply IHt' in H3.
  rewrite swap_not_change_phase in H2.
  apply start_txn_step with (tid:=t0) in H3; auto. auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H4. simpl.
  rewrite swap_not_change_phase in H2; auto.
  rewrite swap_not_change_lock0_2 in H3; auto.
  rewrite swap_not_change_write_version; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3. simpl.
  rewrite swap_not_change_phase in H1; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H2. simpl.
  rewrite swap_not_change_phase in H1; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H4. simpl.
  rewrite swap_not_change_phase in H1; auto.
  apply swap_not_change_in in H2; auto.
  rewrite swap_not_change_lock0_2 in H3; auto.
  apply lock_write_item_step with (tid0:= t0) (v:=v) in H4; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3. simpl.
  rewrite swap_not_change_phase in H1; auto.
  assert (forall v : value,
     In (t0, write_item v) (t' ++ (tid2, a2) :: (tid1, a1) :: t) ->
     In (t0, lock_write_item) (t' ++ (tid2, a2) :: (tid1, a1) :: t)).
  intros. apply swap_not_change_in_rev in H4; auto. apply H2 in H4. apply swap_not_change_in in H4; auto.
  apply seq_point_step with (tid:= t0) in H3; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H5. simpl.
  rewrite swap_not_change_phase in H2; auto.
  rewrite swap_not_change_lock0_2' in H3; auto.
  rewrite swap_not_change_write_version in H4; auto.
  
  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3	. simpl.
  rewrite swap_not_change_phase in H1; auto.
  rewrite swap_not_change_phase in H2; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3	. simpl.
  rewrite swap_not_change_phase in H1; auto.
  rewrite swap_not_change_lock0_2' in H2; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H4. simpl.
  rewrite swap_not_change_phase in H1; auto.
  assert (forall vers : version,
     In (t0, read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t) ->
     In (t0, validate_read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t)).
  intros. apply swap_not_change_in_rev in H5; auto. apply H2 in H5. apply swap_not_change_in in H5; auto.
  assert (forall vers : version,
     In (t0, validate_read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t) ->
     In (t0, read_item vers) (t' ++ (tid2, a2) :: (tid1, a1) :: t)).
  intros. apply swap_not_change_in_rev in H6; auto. apply H3 in H6. apply swap_not_change_in in H6; auto.
  apply commit_txn_step with (tid:= t0) in H4; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H5. simpl.
  rewrite swap_not_change_phase in H2; auto.
  rewrite swap_not_change_lock0_2' in H3; auto.
  rewrite swap_not_change_last_write in H4; auto.
  rewrite swap_not_change_write_version; auto.
  apply complete_write_item_step with (tid0:= t0) (val:= val) in H5; auto.

  assert (sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)) as CP; auto.
  apply IHt' in H3	. simpl.
  rewrite swap_not_change_phase in H1; auto.
  rewrite swap_not_change_lock0_2' in H2; auto.
Qed.

Lemma tid_phase_gt0 tid a t:
  sto_trace t
  -> In (tid, a) t
  -> trace_tid_phase tid t > 0.
Proof.
  intros.
  apply in_split in H0.
  destruct H0. destruct H0.
  rewrite H0 in *. clear H0.
  induction x.
  simpl in *. destruct (Nat.eq_dec tid tid); try contradiction.
  destruct a; simpl; auto; try omega.
  destruct a0. simpl.
  destruct (Nat.eq_dec tid t0). destruct a0; simpl; auto; try omega.
  simpl in H.
  apply sto_trace_cons in H. auto.
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

Lemma not_equal_phase6 t2 tid1 a1 tid2 a2 t:
  sto_trace (t2 ++ (tid1, a1) :: (tid2, a2) :: t)
  -> tid1 <> tid2
  -> (forall tid0,
     trace_tid_phase tid0 (t2 ++ (tid1, a1) :: (tid2, a2) :: t) > 0 ->
     trace_tid_phase tid0 (t2 ++ (tid1, a1) :: (tid2, a2) :: t) = 4)
  -> action_phase a1 <> 6 /\ action_phase a2 <> 6.
Proof.
  intros.
  assert (In (tid1, a1) (t2 ++ (tid1, a1) :: (tid2, a2) :: t)). apply in_or_app. simpl. auto.
  assert (In (tid2, a2) (t2 ++ (tid1, a1) :: (tid2, a2) :: t)). apply in_or_app. simpl. auto.
  apply tid_phase_gt0 in H2; auto.
  apply tid_phase_gt0 in H3; auto.
  apply H1 in H2. apply H1 in H3. clear H1.
  assert (sto_trace (t2 ++ (tid1, a1) :: (tid2, a2) :: t)). auto.
  apply phase_increase_app with (tid0:= tid1) in H.
  apply phase_increase_app with (tid0:= tid2) in H1.
  rewrite H2 in *. rewrite H3 in *.
  simpl in *.
  destruct (Nat.eq_dec tid1 tid1); try contradiction.
  destruct (Nat.eq_dec tid2 tid1). rewrite e0 in *. try contradiction.
  destruct (Nat.eq_dec tid2 tid2); try contradiction.
  split; intuition.
Qed.
  
Lemma is_not_seq_point_lemma a:
  is_not_seq_point a = true
  -> a <> seq_point.
Proof.
  intros.
  destruct a; intuition; inversion H0.
Qed.

Lemma locked_by_holds t tid1 tid2:
  tid1 <> tid2
  -> tid1 <> 0
  -> tid2 <> 0
  -> locked_by t 0 = tid1
  -> locked_by t tid2 = tid1.
Proof.
  intros.
  induction t; simpl in *. rewrite H2 in H0; try contradiction.
  destruct a. destruct a; auto.
  all: rewrite H2 in H0; try contradiction.
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

Lemma phase_4_has_commit tid t:
  sto_trace t ->
  trace_tid_phase tid t = 4 
  -> In (tid, commit_txn) t.
Proof.
  intros ST PH4.
  induction ST.
  simpl in *; omega.
  all: simpl in *; destruct (Nat.eq_dec tid tid0); try omega; auto.
  all: rewrite e in *; auto.
Qed.

Lemma vers_increase_app t1 t2:
  sto_trace (t1 ++ t2) ->
  trace_write_version (t1 ++ t2) >= trace_write_version t2.
Proof.
  induction t1; intros.
  simpl. auto.
  destruct a. 
  assert (sto_trace (((t, a) :: t1) ++ t2)). auto.
  simpl in H. destruct a.
  all: apply sto_trace_cons in H; simpl; auto.
  inversion H0.
  apply IHt1 in H. omega.
Qed.

Lemma not_cust1 t' t tid1 tid2 vers:
  tid1 <> tid2
  -> vers = trace_write_version ((tid2, complete_write_item (S (trace_write_version t))) :: t)
  -> committed_unconflicted_sto_trace (t' ++ (tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t) 
  -> False.
Proof.
  intros NE V CUST.
  inversion CUST.
  assert (trace_tid_phase tid1 (t' ++ (tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t) > 0).
  {
    clear H0 H1 CUST V.
    induction t'; simpl.
    destruct (Nat.eq_dec tid1 tid1). omega.
    destruct (Nat.eq_dec tid1 tid2); try contradiction.
    destruct a.
    destruct (Nat.eq_dec tid1 t0); auto.
    assert (In (t0, a) (((t0, a) :: t') ++ (tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t)). simpl; auto. apply tid_nonzero in H0.
    destruct a; simpl; auto; try omega. auto.
    simpl in H. apply sto_trace_cons in H. auto.
  }
  apply H0 in H2.
  simpl in *.
  clear H0.
  assert (In (tid1, commit_txn) t').
  {
    assert (In (tid1, commit_txn) (t' ++ (tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t)).
    apply phase_4_has_commit in H2. auto. auto.
    assert (trace_tid_phase tid1 ((tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t) = 3).
    simpl. destruct (Nat.eq_dec tid1 tid1); try contradiction; auto.
    apply phase_increase_in_app in H0; auto.
    simpl. destruct (Nat.eq_dec tid1 tid1); try contradiction; auto.
  }
  assert (exists t'' t''', sto_trace (t''' ++ (tid1, commit_txn) :: t'' ++ (tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t)).
  apply in_split in H0.
  destruct H0. destruct H0.
  exists x0. exists x.
  rewrite H0 in H. rewrite <- app_assoc in H. auto.
  inversion H3.
  inversion H4.
  apply sto_trace_app in H5.
  inversion H5.
  clear H3 H4.
  assert (In (tid1, validate_read_item vers) (x ++ (tid1, validate_read_item vers) :: (tid2, complete_write_item (S (trace_write_version t))) :: t)).
  intuition.
  assert (In (tid1, read_item vers) t).
  apply H10 in H3.
  apply in_app_or in H3.
  destruct H3.
  apply in_split in H3.
  destruct H3.
  destruct H3.
  rewrite H3 in H11.
  rewrite <- app_assoc in H11.
  apply sto_trace_app in H11.
  inversion H11.
  assert (trace_tid_phase tid1 ((tid1, validate_read_item (trace_write_version t1)) :: (tid2, complete_write_item (S (trace_write_version t))) :: t) = 3).
  {
    simpl. destruct (Nat.eq_dec tid1 tid1); try contradiction; auto.
  }
  apply phase_increase_app with (tid0:=tid1) in H16.
  rewrite H14 in H16. rewrite H17 in H16.
  omega.
  simpl in H3.
  destruct H3. inversion H3. destruct H3. inversion H3. auto.
  assert (vers <= trace_write_version t).
  apply in_split in H4.
  destruct H4. destruct H4.
  rewrite H4 in H11. rewrite H4 in V.
  apply sto_trace_app in H11.
  apply sto_trace_cons in H11.
  apply sto_trace_cons in H11.
  assert( sto_trace (x1 ++ (tid1, read_item vers) :: x2)).
  auto.
  apply sto_trace_app in H11.
  inversion H11.
  rewrite H15 in H14.
  rewrite <- H14 in V.
  apply vers_increase_app in H12.
  simpl in H12.
  rewrite V in H12.
  rewrite <- H14 in H12.
  omega.
  rewrite V in H12. omega.
Qed.

Lemma locked_by_holds2 t tid1 tid2:
  tid1 <> tid2
  -> sto_trace t
  -> locked_by t 0 = 0
  -> locked_by t tid2 = tid2.
Proof.
  intros.
  induction t. simpl in *. auto. 
  destruct a. assert (sto_trace ((t0, a) :: t)); auto.
  destruct a; apply sto_trace_cons in H0; auto.
  simpl in H1.
  assert (In (t0, lock_write_item) ((t0, lock_write_item) :: t)). simpl; auto. apply tid_nonzero with (tid0:= t0) (a:= lock_write_item) in H2; auto. rewrite H1 in H2. omega.
Qed.

Lemma locked_by_holds3 t tid1 tid2:
  tid1 <> tid2
  -> sto_trace t
  -> locked_by t 0 = tid2
  -> locked_by t tid2 = tid2.
Proof.
  intros.
  induction t. simpl in *. auto. 
  destruct a. assert (sto_trace ((t0, a) :: t)); auto.
  destruct a; apply sto_trace_cons in H0; auto.
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

Lemma write_version_hold x x2 t:
  sto_trace (x2 ++ (t, lock_write_item) :: x)
  -> locked_by (x2 ++ (t, lock_write_item) :: x) 0 = t
  -> trace_write_version (x2 ++ (t, lock_write_item) :: x) = trace_write_version x.
Proof.
  intros ST L.
  induction x2.
  simpl in *. auto.
  destruct a. assert (sto_trace (((t0, a) :: x2) ++ (t, lock_write_item) :: x)) as CP; auto.
  destruct a; simpl in ST; apply sto_trace_cons in ST.
  simpl in L; auto.
  simpl in L; auto.
  simpl in L; auto.
  simpl in L; auto.
  simpl in L. rewrite L in CP.
  inversion CP.
  simpl in CP. apply sto_trace_cons in CP.
  assert (locked_by ((t, lock_write_item) :: x) 0 = t). simpl; auto.
  apply phase_2_preserves_lock with (tid0:= t) in CP; auto.
  simpl in L; auto.
  simpl in L; auto.
  simpl in L; auto.
  simpl in L.
  assert (In (t, lock_write_item) (x2 ++ (t, lock_write_item) :: x)).
  apply in_or_app. simpl; auto.
  apply tid_nonzero with (tid0:= t) (a:= lock_write_item) in ST; auto.
  rewrite <- L in ST. omega.
  simpl in L; auto.
  simpl in L.
  assert (In (t, lock_write_item) (x2 ++ (t, lock_write_item) :: x)).
  apply in_or_app. simpl; auto.
  apply tid_nonzero with (tid0:= t) (a:= lock_write_item) in ST; auto.
  rewrite <- L in ST. omega.
  simpl in L; auto.
Qed.

Lemma lock_change x x2 tid1:
  sto_trace (x2 ++ (tid1, lock_write_item) :: x)
  -> forall tid2, locked_by (x2 ++ (tid1, lock_write_item) :: x) tid2 = tid2
  -> tid1 <> tid2
  -> In (tid1, complete_write_item (S (trace_write_version x))) x2
    \/ In (tid1, unlock_write_item) x2.
Proof.
  induction x2; 
  intros ST tid2 L NE; simpl; auto.
  destruct a. assert (sto_trace (((t, a) :: x2) ++ (tid1, lock_write_item) :: x)) as CP; auto.
  destruct a; simpl in *; auto.
  all: apply sto_trace_cons in ST.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  inversion CP; subst.
  apply locked_by_holds2 with (tid1:= tid1) (tid2:= tid2) in H3; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  inversion CP.
  destruct (Nat.eq_dec tid1 t). rewrite e. auto.
  apply locked_by_holds3 with (tid1:= tid1) in H2; auto.
  apply IHx2 with (tid2:= t) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
  inversion CP.
  destruct (Nat.eq_dec tid1 t). rewrite e in *. 
  apply write_version_hold in H5; auto. rewrite H5. auto.
  apply locked_by_holds3 with (tid1:= tid1) in H3; auto.
  apply IHx2 with (tid2:= t) in ST; auto. destruct ST; auto.
  apply IHx2 with (tid2:= tid2) in ST; auto. destruct ST; auto.
Qed.

Lemma not_cust2 t' t tid1 tid2:
  tid1 <> tid2
  -> committed_unconflicted_sto_trace (t' ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t)
  -> False.
Proof.
  intros NE CUST.
  inversion CUST.
  assert (trace_tid_phase tid2 (t' ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t) > 0).
  {
    clear H0 H1 CUST.
    induction t'; simpl.
    destruct (Nat.eq_dec tid2 tid1); try rewrite e in NE; try contradiction.
    destruct (Nat.eq_dec tid2 tid2); omega.
    destruct a.
    destruct (Nat.eq_dec tid2 t0); auto.
    assert (In (t0, a) (((t0, a) :: t') ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t)). simpl; auto. apply tid_nonzero in H0.
    destruct a; simpl; auto; try omega. auto.
    simpl in H. apply sto_trace_cons in H. auto.
  }
  apply H0 in H2.
  simpl in *.
  clear H0.
  assert (In (tid2, commit_txn) t').
  {
    assert (In (tid2, commit_txn) (t' ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t)).
    apply phase_4_has_commit in H2. auto. auto.
    assert (trace_tid_phase tid2 ((tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t) = 1).
    simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in NE; try contradiction. destruct (Nat.eq_dec tid2 tid2); try contradiction; auto.
    apply phase_increase_in_app in H0; auto.
    simpl. destruct (Nat.eq_dec tid2 tid1); try contradiction; auto. destruct (Nat.eq_dec tid2 tid2); try contradiction; auto.
  }
  assert (exists t'' t''', sto_trace (t''' ++ (tid2, commit_txn) :: t'' ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t)).
  apply in_split in H0.
  destruct H0. destruct H0.
  exists x0. exists x. rewrite H0 in CUST.
  rewrite H0 in H. rewrite <- app_assoc in H. auto.
  apply in_split in H0.
  destruct H0. destruct H0. rewrite H0 in CUST. rewrite H0 in H.
  clear H3. rewrite <- app_assoc in H.
  apply sto_trace_app in H.
  inversion H.
  assert (In (tid2, read_item (trace_write_version t)) (x0 ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t)).
  intuition.
  assert (In (tid2, validate_read_item (trace_write_version t)) x0).
  remember (trace_write_version t) as vers.
  apply H6 in H9.
  apply in_app_or in H9.
  destruct H9. auto.
  simpl in H9. destruct H9. inversion H9. destruct H9. inversion H9.
  apply in_split in H9.
  destruct H9.
  destruct H9.
  rewrite H9 in H8.
  apply sto_trace_app in H8.
  apply sto_trace_cons in H8.
  inversion H8.
  apply phase_increase_app with (tid0:=tid2) in H15.
  rewrite H13 in H15. simpl in H15. destruct (Nat.eq_dec tid2 tid2); try contradiction. omega.
  apply in_split in H10.
  destruct H10. destruct H10.
  rewrite H10 in *. rewrite <- app_assoc in H8. 
  apply sto_trace_app in H8. simpl in H8.
  inversion H8.
  subst.
  clear H H2 H5 H6 H7 H8 H9 H14.
  assert (locked_by (x2 ++ (tid1, lock_write_item) :: (tid2, read_item (trace_write_version t)) :: t) tid2 = tid2 -> In (tid1, complete_write_item (S (trace_write_version t))) x2).
  assert (trace_write_version t = trace_write_version ((tid2, read_item (trace_write_version t)) :: t)). simpl; auto.
  remember ((tid2, read_item (trace_write_version t)) :: t) as x'.
  rewrite H. intros.
  apply lock_change with (x:= x') in H0. auto.
  destruct H0; auto.
  inversion CUST.
  assert (trace_tid_phase tid1 ((x ++ (tid2, commit_txn) :: x1 ++ (tid2, validate_read_item (trace_write_version t)) :: x2) ++ (tid1, lock_write_item) :: x') > 0). 
  apply phase_increase_app with (tid0:= tid1) in H1. simpl in H1.
  destruct (Nat.eq_dec tid1 tid1); try contradiction; auto; try omega.
  apply H2 in H4.
  apply in_split in H0. destruct H0. destruct H0.
  rewrite H0 in H4. rewrite H0 in H1. simpl in H1.
  rewrite <- app_assoc in H1.   
  assert (sto_trace (x ++ ((tid2, commit_txn) :: x1 ++ (tid2, validate_read_item (trace_write_version t)) :: x0 ++ (tid1, unlock_write_item) :: x3) ++ (tid1, lock_write_item) :: x')) as CP; auto.
  apply phase_increase_app with (tid0:= tid1) in H1. simpl in H1.
  destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply sto_trace_app in CP. simpl in CP. apply sto_trace_cons in CP.
  rewrite <- app_assoc in CP.
  assert (sto_trace (x1 ++ ((tid2, validate_read_item (trace_write_version t)) :: x0 ++ (tid1, unlock_write_item) :: x3) ++ (tid1, lock_write_item) :: x')) as CP2; auto.
  apply phase_increase_app with (tid0:= tid1) in CP. simpl in CP.
  destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply sto_trace_app in CP2. simpl in CP2. apply sto_trace_cons in CP2.
  rewrite <- app_assoc in CP2.
  apply phase_increase_app with (tid0:= tid1) in CP2. simpl in CP2.
  destruct (Nat.eq_dec tid1 tid1); try contradiction; auto.
  rewrite <- app_assoc in H4. simpl in H4. rewrite H4 in *.
  rewrite <- app_assoc in H1. simpl in H1.
  rewrite <- app_assoc in CP. simpl in CP.
  assert (trace_tid_phase tid1 (x1 ++ (tid2, validate_read_item (trace_write_version t)) :: x0 ++ (tid1, unlock_write_item) :: x3 ++ (tid1, lock_write_item) :: x') >= 6). intuition.
  rewrite <- app_assoc in H1. simpl in H1.
  assert (4 >= 6). intuition. omega. auto. auto.
  apply H in H15.
  apply in_split in H15. destruct H15. destruct H0.
  rewrite H0 in H16. rewrite H0 in H17.
  rewrite <- app_assoc in H16. rewrite <- app_assoc in H17.
  apply vers_increase_app in H17. 
  rewrite H16 in H17. simpl in H17. omega.
Qed.

Lemma swap1_preserve_st_strong t tid:
  sto_trace t
  -> (forall t2, committed_unconflicted_sto_trace (t2 ++ t)
  -> sto_trace (t2 ++ (swap1 t tid))).
Proof.
  intros ST.
  functional induction (swap1 t tid).
  intros.
  apply sto_trace_cons in ST.
  assert ((t2 ++ (tid1, a1) :: (tid1, a2) :: tail') 
        = t2 ++ [(tid1, a1)] ++ (tid1, a2) :: tail'). auto.
  rewrite H0 in H.
  apply IHt0 with (t2:= t2 ++ [(tid1, a1)]) in ST. 
  assert (((t2 ++ [(tid1, a1)]) ++ swap1 ((tid1, a2) :: tail') tid0) 
       = (t2 ++ (tid1, a1) :: swap1 ((tid1, a2) :: tail') tid0)).
  rewrite <- app_assoc. auto.
  rewrite H1 in ST; auto. rewrite <- app_assoc; auto.
  
  intros t2 CUST. clear e1.
  apply andb_true_iff in e2; destruct e2 as [e2 SP].
  apply andb_true_iff in e2; destruct e2 as [tid01 GT3].
  apply leb_complete in GT3. apply is_not_seq_point_lemma in SP. 

  assert (sto_trace ((tid1, a1) :: (tid2, a2) :: tail')) as ST1. auto.
  assert (sto_trace ((tid1, a1) :: (tid2, a2) :: tail')) as ST2. auto.
  apply sto_trace_cons in ST1. 
  inversion CUST.
  apply not_equal_phase6 in H0; auto. destruct H0 as [NE61 NE62].
  inversion ST2; rewrite <- H2 in *; simpl in GT3; try omega; try contradiction.

  assert (trace_tid_phase tid1 tail' = 3). simpl in H4; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  inversion ST1; rewrite <- H10 in *; simpl in NE62; try omega.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 0); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply start_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, validate_read_item vers) :: tail') 0 = 0); simpl; auto. 
  assert (trace_write_version tail' = trace_write_version ((tid1, validate_read_item vers) :: tail')); simpl; auto. rewrite H17.
  apply read_item_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. rewrite H5 in _x. contradiction.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall v : value,
      In (tid2, write_item v) ((tid1, validate_read_item vers) :: tail') -> In (tid2, lock_write_item) ((tid1, validate_read_item vers) :: tail')). 
  intros. simpl in H16. destruct H16. inversion H16; try contradiction.
  apply H13 in H16. simpl. auto.
  apply seq_point_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  rewrite H6 in H14. rewrite <- H14 in *.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, validate_read_item vers) :: tail') tid2 = tid2); simpl; auto. 
  apply validate_read_item_step with (tid0:= tid2) (vers:= vers) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall vers0 : version,
      In (tid2, read_item vers0) ((tid1, validate_read_item vers) :: tail') -> In (tid2, validate_read_item vers0) ((tid1, validate_read_item vers) :: tail')). 
  intros. simpl in H17. destruct H17. inversion H17; try contradiction.
  apply H13 in H17. simpl. auto.
  assert (forall vers0 : version,
      In (tid2, validate_read_item vers0) ((tid1, validate_read_item vers) :: tail') -> In (tid2, read_item vers0) ((tid1, validate_read_item vers) :: tail')). 
  intros. simpl in H18. destruct H18. inversion H18; try contradiction.
  apply H14 in H18. simpl. auto.
  apply commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  rewrite H11 in *. apply not_cust1 in CUST; auto. inversion CUST.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 4); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, validate_read_item vers) :: tail') 0 <> tid2); simpl; auto. 
  apply commit_done_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H4. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  assert (forall vers0 : version,
     In (tid1, read_item vers0) tail' ->
     In (tid1, validate_read_item vers0) tail').
  intros. simpl in H5.
  assert ((tid2, a2) = (tid1, read_item vers0) \/ In (tid1, read_item vers0) tail'). auto. apply H5 in H9. destruct H9. inversion H9. rewrite H11 in *. contradiction. auto.
  assert (forall vers0 : version,
     In (tid1, validate_read_item vers0) tail' ->
     In (tid1, read_item vers0) tail').
  intros. simpl in H6.
  assert ((tid2, a2) = (tid1, validate_read_item vers0) \/ In (tid1, validate_read_item vers0) tail'). auto. apply H6 in H10.
  destruct H10. inversion H10. rewrite H12 in *. contradiction. auto.
  apply sto_trace_cons in H7.
  apply commit_txn_step with (tid:= tid1) in H7; auto.

  inversion ST1; rewrite <- H11 in *; simpl in NE62; try omega.
  
  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 0); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply start_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') 0 = 0); simpl; auto. 
  assert (trace_write_version tail' = trace_write_version ((tid1, commit_txn) :: tail')); simpl; auto. rewrite H18.
  apply read_item_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (In (tid2, write_item v) ((tid1, commit_txn) :: tail')); simpl; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall v : value,
      In (tid2, write_item v) ((tid1, commit_txn) :: tail') -> In (tid2, lock_write_item) ((tid1, commit_txn) :: tail')). 
  intros. simpl in H17. destruct H17. inversion H17; try contradiction.
  apply H14 in H17. simpl. auto.
  apply seq_point_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') tid2 = tid2); simpl; auto. 
  apply validate_read_item_step with (tid0:= tid2) (vers:= vers) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall vers0 : version,
      In (tid2, read_item vers0) ((tid1, commit_txn) :: tail') -> In (tid2, validate_read_item vers0) ((tid1, commit_txn) :: tail')). 
  intros. simpl in H18. destruct H18. inversion H18; try contradiction.
  apply H14 in H18. simpl. auto.
  assert (forall vers0 : version,
      In (tid2, validate_read_item vers0) ((tid1, commit_txn) :: tail') -> In (tid2, read_item vers0) ((tid1, commit_txn) :: tail')). 
  intros. simpl in H19. destruct H19. inversion H19; try contradiction.
  apply H15 in H19. simpl. auto.
  apply commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 4); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') 0 = tid2); simpl; auto.
  assert (trace_tid_last_write tid2 ((tid1, commit_txn) :: tail') = Some val); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, commit_txn) :: tail')); simpl; auto. rewrite H20.
  apply complete_write_item_step with (tid0:= tid2) (val:= val) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: tail') = 4); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') 0 <> tid2); simpl; auto. 
  apply commit_done_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  
  simpl in H4. destruct (Nat.eq_dec tid1 tid2); try contradiction.

  inversion ST1; rewrite <- H9 in *; simpl in NE62; try omega.
  
  simpl in H5. simpl in H6. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  apply sto_trace_cons in H7. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') = 0); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply start_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. rewrite H5 in H12.
  assert (In (tid1, complete_write_item (S (trace_write_version t))) ((tid1, complete_write_item (S (trace_write_version t))) :: (tid2, read_item (trace_write_version t0)) :: tail')); simpl; auto.
  apply tid_nonzero in H14; auto. rewrite H12 in H14. omega.

  simpl in H5. simpl in H6. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  apply sto_trace_cons in H7. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply write_item_step with (tid:= tid2) (val:= val0) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  simpl in H5. simpl in H6. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  apply sto_trace_cons in H7. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  
  simpl in H5. rewrite H5 in _x. contradiction.

  simpl in H5. simpl in H6. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  apply sto_trace_cons in H7. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall v : value,
      In (tid2, write_item v) ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') -> In (tid2, lock_write_item) ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail')). 
  intros. simpl in H15. destruct H15. inversion H15; try contradiction.
  apply H12 in H15. simpl. auto.
  apply seq_point_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5.
  apply locked_by_holds with (tid2:= tid2) in H5.
  rewrite H5 in H12. contradiction. auto.
  assert (In (tid1, complete_write_item (S (trace_write_version t))) (((tid1, complete_write_item (S (trace_write_version t))) :: (tid2, validate_read_item vers) :: tail'))); simpl. auto. apply tid_nonzero in H15; auto.
  assert (In (tid2, validate_read_item vers) (((tid1, complete_write_item (S (trace_write_version t))) :: (tid2, validate_read_item vers) :: tail'))); simpl. auto. apply tid_nonzero in H15; auto.

  simpl in H5. simpl in H6. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  apply sto_trace_cons in H7. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall vers0 : version,
      In (tid2, read_item vers0) ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') -> In (tid2, validate_read_item vers0) ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail')). 
  intros. simpl in H16. destruct H16. inversion H16; try contradiction.
  apply H12 in H16. simpl. auto.
  assert (forall vers0 : version,
      In (tid2, validate_read_item vers0) ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') -> In (tid2, read_item vers0) ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail')). 
  intros. simpl in H17. destruct H17. inversion H17; try contradiction.
  apply H13 in H17. simpl. auto.
  apply commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. 
  assert (In (tid1, complete_write_item (S (trace_write_version t))) ((tid1, complete_write_item (S (trace_write_version t))):: (tid2, complete_write_item (S (trace_write_version t0))) :: tail')); simpl; auto.
  apply tid_nonzero in H15; auto. rewrite H5 in H15. omega.

  simpl in H5. simpl in H6. destruct (Nat.eq_dec tid1 tid2); try contradiction.
  apply sto_trace_cons in H7. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') = 4); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, complete_write_item (S (trace_write_version tail'))) :: tail') 0 <> tid2); simpl. 
  assert (In (tid2, commit_done_txn) ((tid1, complete_write_item (S (trace_write_version t))) :: (tid2, commit_done_txn) :: tail')); simpl; auto.
  apply tid_nonzero in H15; auto.
  apply commit_done_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  
  simpl in H4. destruct (Nat.eq_dec tid1 tid2); try contradiction.

  inversion ST1; rewrite <- H8 in *; simpl in NE62; try omega.
  
  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 0); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') 0 = 0); simpl; auto. 
  assert (trace_write_version tail' = trace_write_version ((tid1, commit_done_txn) :: tail')); simpl; auto. rewrite H15.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (In (tid2, write_item v) ((tid1, commit_done_txn) :: tail')); simpl; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.
  rewrite H12.
  assert (In (tid1, commit_done_txn) ((tid1, commit_done_txn) :: (tid2, lock_write_item) :: tail')); simpl. auto.
  apply tid_nonzero in H14; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall v : value,
      In (tid2, write_item v) ((tid1, commit_done_txn) :: tail') -> In (tid2, lock_write_item) ((tid1, commit_done_txn) :: tail')). 
  intros. simpl in H14. destruct H14. inversion H14; try contradiction.
  apply H11 in H14. simpl. auto.
  apply seq_point_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') tid2 = tid2); simpl; auto. 
  apply validate_read_item_step with (tid0:= tid2) (vers:= vers) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 3); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (forall vers0 : version,
      In (tid2, read_item vers0) ((tid1, commit_done_txn) :: tail') -> In (tid2, validate_read_item vers0) ((tid1, commit_done_txn) :: tail')). 
  intros. simpl in H15. destruct H15. inversion H15; try contradiction.
  apply H11 in H15. simpl. auto.
  assert (forall vers0 : version,
      In (tid2, validate_read_item vers0) ((tid1, commit_done_txn) :: tail') -> In (tid2, read_item vers0) ((tid1, commit_done_txn) :: tail')). 
  intros. simpl in H16. destruct H16. inversion H16; try contradiction.
  apply H12 in H16. simpl. auto.
  apply commit_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 4); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') 0 = tid2); simpl; auto.
  assert (trace_tid_last_write tid2 ((tid1, commit_done_txn) :: tail') = Some val); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, commit_done_txn) :: tail')); simpl; auto. rewrite H17.
  apply complete_write_item_step with (tid0:= tid2) (val:= val) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.
  rewrite H11. auto.

  simpl in H5. apply sto_trace_cons in H6. apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: tail') = 4); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') 0 <> tid2); simpl; auto. 
  apply commit_done_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app in H; subst; auto.

  intros t2 CUST. clear e1 e2.
  apply andb_true_iff in e3; destruct e3 as [e3 LT3].
  apply Nat.ltb_lt in LT3.

  assert (sto_trace ((tid1, a1) :: (tid2, a2) :: tail')) as ST1. auto.
  assert (sto_trace ((tid1, a1) :: (tid2, a2) :: tail')) as ST2. auto.
  apply sto_trace_cons in ST1. 
  inversion CUST.
  apply not_equal_phase6 in H0; auto. destruct H0 as [NE61 NE62].
  
  inversion ST1; rewrite <- H2 in *; simpl in LT3; try omega; try contradiction.
  
  assert (trace_tid_phase tid2 ((tid1, a1) :: tail') = 0); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.

  inversion ST2; rewrite <- H9 in *.
  
  simpl in H12; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply start_txn_step with (tid:= tid1) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12. simpl.
  apply read_item_step with (tid0:= tid1) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply write_item_step with (tid:= tid1) (val:= val) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid1) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12. destruct H12. inversion H12. simpl in H13.
  apply lock_write_item_step with (tid0:= tid1) (v:= v) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H12. assert (forall v : value, In (tid1, write_item v) tail' -> In (tid1, lock_write_item) tail'). intros. assert ((tid2, start_txn) = (tid1, write_item v) \/ In (tid1, write_item v) tail'); auto. apply H12 in H15. destruct H15. inversion H15. auto.
  apply seq_point_step with (tid:= tid1) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12. simpl in H13.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.
  
  simpl in NE61; omega.
  simpl in NE61; omega.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H12. assert (forall vers : version, In (tid1, read_item vers) tail' -> In (tid1, validate_read_item vers) tail'). intros. assert ((tid2, start_txn) = (tid1, read_item vers) \/ In (tid1, read_item vers) tail'). auto. apply H12 in H16. destruct H16. inversion H16. auto. assert (forall vers : version, In (tid1, validate_read_item vers) tail' -> In (tid1, read_item vers) tail'). intros. assert ((tid2, start_txn) = (tid1, validate_read_item vers) \/ In (tid1, validate_read_item vers) tail'). auto. apply H13 in H17. destruct H17. inversion H17. auto.
  apply commit_txn_step with (tid:= tid1) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12. simpl in H13; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12.
  apply commit_done_step with (tid0:= tid1) in H6; auto.
  apply start_txn_step with (tid:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, a1) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.

  inversion ST2; rewrite <- H9 in *.
  
  simpl in H12; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply start_txn_step with (tid:= tid1) in H6; auto.
  assert (locked_by ((tid1, start_txn) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, start_txn) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12. simpl.
  apply read_item_step with (tid0:= tid1) in H6; auto.
  assert (locked_by ((tid1, read_item (trace_write_version tail')) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, read_item (trace_write_version tail')) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply write_item_step with (tid:= tid1) (val:= val) in H6; auto.
  assert (locked_by ((tid1, write_item val) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, write_item val) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid1) in H6; auto.
  assert (locked_by ((tid1, try_commit_txn) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, try_commit_txn) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  rewrite H3 in *. apply not_cust2 with (tid2:= tid2) in CUST; auto.
  inversion CUST.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H12. assert (forall v : value, In (tid1, write_item v) tail' -> In (tid1, lock_write_item) tail'). intros. assert ((tid2, read_item (trace_write_version t)) = (tid1, write_item v) \/ In (tid1, write_item v) tail'); auto. apply H12 in H15. destruct H15. inversion H15. auto.
  apply seq_point_step with (tid:= tid1) in H6; auto.
  assert (locked_by ((tid1, seq_point) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, seq_point) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12. simpl in H13.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H6; auto.
  assert (locked_by ((tid1, validate_read_item vers) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, validate_read_item vers) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in NE61; omega.
  simpl in NE61; omega.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H12. assert (forall vers : version, In (tid1, read_item vers) tail' -> In (tid1, validate_read_item vers) tail'). intros. assert ((tid2, read_item (trace_write_version t)) = (tid1, read_item vers) \/ In (tid1, read_item vers) tail'). auto. apply H12 in H16. destruct H16. inversion H16. auto. 
  simpl in H13. assert (forall vers : version, In (tid1, validate_read_item vers) tail' -> In (tid1, read_item vers) tail'). intros. assert ((tid2, read_item (trace_write_version t)) = (tid1, validate_read_item vers) \/ In (tid1, validate_read_item vers) tail'). auto. apply H13 in H17. destruct H17. inversion H17. rewrite H19 in *; try contradiction. auto.
  apply commit_txn_step with (tid:= tid1) in H6; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, commit_txn) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H12. rewrite H5 in H12.
  assert (In (tid1, complete_write_item (S (trace_write_version t0))) ((tid1, complete_write_item (S (trace_write_version t0))) :: (tid2, read_item (trace_write_version t)) :: tail')); simpl; auto.
  apply tid_nonzero in H15; auto. rewrite H12 in H15. omega.

  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H12.
  apply commit_done_step with (tid0:= tid1) in H6; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') 0 = 0); simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, commit_done_txn) :: tail')) as WV; simpl; auto. rewrite WV.
  apply read_item_step with (tid0:= tid2) in H6; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, a1) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.

  inversion ST2; rewrite <- H8 in *.
  
  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply start_txn_step with (tid:= tid1) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. simpl.
  apply read_item_step with (tid0:= tid1) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H9; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply write_item_step with (tid:= tid1) (val:= val0) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H9; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid1) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. destruct H11. inversion H11. rewrite H15 in _x; try contradiction. simpl in H12.
  apply lock_write_item_step with (tid0:= tid1) (v:= v) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H11. assert (forall v : value, In (tid1, write_item v) tail' -> In (tid1, lock_write_item) tail'). intros. assert ((tid2,  write_item val) = (tid1, write_item v) \/ In (tid1, write_item v) tail'); auto. apply H11 in H14. destruct H14. inversion H14. auto.
  apply seq_point_step with (tid:= tid1) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. simpl in H12.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.
  
  simpl in NE61; omega.
  simpl in NE61; omega.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H11. assert (forall vers : version, In (tid1, read_item vers) tail' -> In (tid1, validate_read_item vers) tail'). intros. assert ((tid2, write_item val) = (tid1, read_item vers) \/ In (tid1, read_item vers) tail'). auto. apply H11 in H15. destruct H15. inversion H15. auto.
  simpl in H12. assert (forall vers : version, In (tid1, validate_read_item vers) tail' -> In (tid1, read_item vers) tail'). intros. assert ((tid2, write_item val) = (tid1, validate_read_item vers) \/ In (tid1, validate_read_item vers) tail'). auto. apply H12 in H16. destruct H16. inversion H16. auto.
  apply commit_txn_step with (tid:= tid1) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. simpl in H12; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val0) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11.
  apply commit_done_step with (tid0:= tid1) in H5; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, a1) :: tail') = 1); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.

  inversion ST2; rewrite <- H8 in *.
  
  simpl in H11; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply start_txn_step with (tid:= tid1) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. simpl.
  apply read_item_step with (tid0:= tid1) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H9; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply write_item_step with (tid:= tid1) (val:= val) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H9; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid1) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. destruct H11. inversion H11. simpl in H12.
  apply lock_write_item_step with (tid0:= tid1) (v:= v) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H11. assert (forall v : value, In (tid1, write_item v) tail' -> In (tid1, lock_write_item) tail'). intros. assert ((tid2,  try_commit_txn) = (tid1, write_item v) \/ In (tid1, write_item v) tail'); auto. apply H11 in H14. destruct H14. inversion H14. auto.
  apply seq_point_step with (tid:= tid1) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. simpl in H12.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.
  
  simpl in NE61; omega.
  simpl in NE61; omega.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H11. assert (forall vers : version, In (tid1, read_item vers) tail' -> In (tid1, validate_read_item vers) tail'). intros. assert ((tid2, try_commit_txn) = (tid1, read_item vers) \/ In (tid1, read_item vers) tail'). auto. apply H11 in H15. destruct H15. inversion H15. auto.
  simpl in H12. assert (forall vers : version, In (tid1, validate_read_item vers) tail' -> In (tid1, read_item vers) tail'). intros. assert ((tid2, try_commit_txn) = (tid1, validate_read_item vers) \/ In (tid1, validate_read_item vers) tail'). auto. apply H12 in H16. destruct H16. inversion H16. auto.
  apply commit_txn_step with (tid:= tid1) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11. simpl in H12; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H10; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H11.
  apply commit_done_step with (tid0:= tid1) in H5; auto.
  apply try_commit_txn_step with (tid:= tid2) in H5; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, a1) :: tail') = 2); simpl; destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  assert (In (tid2, write_item v) ((tid1, a1) :: tail')). simpl; auto.

  inversion ST2; rewrite <- H11 in *.
  
  simpl in H14; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply start_txn_step with (tid:= tid1) in H7; auto.
  assert (locked_by ((tid1, start_txn) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H13; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. simpl in H14. simpl. 
  rewrite H12 in *.
  assert (trace_write_version ((tid2, lock_write_item) :: tail') = trace_write_version tail'); simpl; auto. rewrite H16 in *.
  apply read_item_step with (tid0:= tid1) in H7; auto.
  assert (locked_by ((tid1, read_item (trace_write_version t0)) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H12; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply write_item_step with (tid:= tid1) (val:= val) in H7; auto.
  assert (locked_by ((tid1, write_item v) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H12; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid1) in H7; auto.
  assert (locked_by ((tid1, write_item v) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H15. assert (In (tid2, lock_write_item) ((tid1, lock_write_item) :: (tid2, lock_write_item) :: tail')); simpl; auto.
  apply tid_nonzero in H17; auto. rewrite H15 in H17. omega.

  simpl in H13; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H14. assert (forall v0 : value, In (tid1, write_item v0) tail' -> In (tid1, lock_write_item) tail'). intros. assert ((tid2, lock_write_item) = (tid1, write_item v0) \/ In (tid1, write_item v0) tail'); auto. apply H14 in H17. destruct H17. inversion H17. rewrite H19 in _x. contradiction. auto.
  apply seq_point_step with (tid:= tid1) in H7; auto.
  assert (locked_by ((tid1, seq_point) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H14. contradiction.

  simpl in NE61; omega.
  simpl in NE61; omega.

  simpl in H13; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto.
  simpl in H14. assert (forall vers : version, In (tid1, read_item vers) tail' -> In (tid1, validate_read_item vers) tail'). intros. assert ((tid2, lock_write_item) = (tid1, read_item vers) \/ In (tid1, read_item vers) tail'). auto. apply H14 in H18. destruct H18. inversion H18. auto.
  simpl in H15. assert (forall vers : version, In (tid1, validate_read_item vers) tail' -> In (tid1, read_item vers) tail'). intros. assert ((tid2, lock_write_item) = (tid1, validate_read_item vers) \/ In (tid1, validate_read_item vers) tail'). auto. apply H15 in H19. destruct H19. inversion H19. auto.
  apply commit_txn_step with (tid:= tid1) in H7; auto.
  assert (locked_by ((tid1, commit_txn) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  simpl in H14. contradiction.

  simpl in H13; destruct (Nat.eq_dec tid1 tid2); try contradiction; auto. 
  assert (locked_by tail' 0 <> tid1). rewrite H6.
  assert (In (tid1, commit_done_txn) ((tid1, commit_done_txn) :: (tid2, lock_write_item) :: tail')); simpl; auto.
  apply tid_nonzero in H16; auto.
  apply commit_done_step with (tid0:= tid1) in H7; auto.
  assert (locked_by ((tid1, commit_done_txn) :: tail') 0 = 0); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app2 in H; subst; auto.

  intros.
  apply sto_trace_cons in ST.
  assert ((t2 ++ (tid1, a1) :: (tid2, a2) :: tail') 
        = t2 ++ [(tid1, a1)] ++ (tid2, a2) :: tail'). auto.
  rewrite H0 in H.
  apply IHt0 with (t2:= t2 ++ [(tid1, a1)]) in ST. 
  assert (((t2 ++ [(tid1, a1)]) ++ swap1 ((tid2, a2) :: tail') tid0) 
       = (t2 ++ (tid1, a1) :: swap1 ((tid2, a2) :: tail') tid0)).
  rewrite <- app_assoc. auto.
  rewrite H1 in ST; auto. rewrite <- app_assoc; auto.
  
  all: intros; inversion H; auto.

Qed.


Lemma swap1_preserve_st t tid:
  committed_unconflicted_sto_trace t
  -> sto_trace (swap1 t tid).
Proof.
  intros.
  inversion H.
  apply swap1_preserve_st_strong with (t2 := []).
  auto. simpl. auto.
Qed.


Lemma swap1_preserve_phase4 t:
  committed_unconflicted_sto_trace t
  -> (forall tid tid0, trace_tid_phase tid (swap1 t tid0) > 0 -> trace_tid_phase tid (swap1 t tid0) = 4).
Proof.
  intros.
  induction H.
  rewrite <- swap1_not_change_phase with (tid0:= tid1) in H0.
  rewrite <- swap1_not_change_phase with (tid0:= tid1).
  apply H1 in H0. auto.
Qed.

Lemma swap1_preserve_cust t :
  committed_unconflicted_sto_trace t
  -> (forall tid, committed_unconflicted_sto_trace (swap1 t tid)).
Proof.
  intros CUST tid.
  assert (committed_unconflicted_sto_trace t) as COPY. auto.
  apply swap1_preserve_st with (tid:= tid) in CUST.
  apply construct_cust. auto.
  intros.
  apply swap1_preserve_phase4 with (tid0:= tid) (tid:= tid0) in COPY.
  auto. auto.
Qed.

Lemma swaps_preserve_cust num:
  forall t, committed_unconflicted_sto_trace t
  -> (forall tid, committed_unconflicted_sto_trace (swaps t tid num)).
Proof.
  induction num;
  intros t CUST tid.
  simpl. auto.
  simpl.
  apply IHnum.
  now apply swap1_preserve_cust with (tid:= tid) in CUST.
Qed.

Lemma create_serial_trace_is_cust_strong l:
  forall t, committed_unconflicted_sto_trace t
  -> committed_unconflicted_sto_trace (create_serialized_trace t l).
Proof.
  induction l;
  intros t CUST. 
  simpl. auto.
  simpl.
  apply swaps_preserve_cust with (num:= (length t * length t)) (tid:= a) in CUST.
  apply IHl. auto.
Qed.

(******************************************)
Theorem create_serial_trace_is_cust t:
  committed_unconflicted_sto_trace t
  -> committed_unconflicted_sto_trace (create_serialized_trace t (seq_list t)).
Proof.
  intros CUST.
  apply create_serial_trace_is_cust_strong with (l:= seq_list t). auto.
Qed.
(******************************************)

Lemma swap1_does_not_reorder t:
  committed_unconflicted_sto_trace t
  -> forall tid tid0, filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (swap1 t tid0).
Proof.
  intros CUST tid tid0.
  induction CUST as [t ST IN]. clear IN.
  functional induction (swap1 t tid0).
  apply sto_trace_cons in ST; apply IHt0 in ST.
  simpl in *.
  destruct (Nat.eq_dec tid1 tid); subst.
  rewrite <- beq_nat_refl in *. rewrite ST. auto.
  apply Nat.eqb_neq in n. rewrite n in *. auto.
  simpl.
  destruct (Nat.eq_dec tid1 tid); subst.
  rewrite <- beq_nat_refl in *.
  destruct (Nat.eq_dec tid2 tid); subst. contradiction.
  apply Nat.eqb_neq in n. rewrite n in *. auto.
  apply Nat.eqb_neq in n. rewrite n in *. 
  destruct (Nat.eq_dec tid2 tid); subst.
  rewrite <- beq_nat_refl in *. auto.
  apply Nat.eqb_neq in n0. rewrite n0 in *. auto.
  simpl.
  destruct (Nat.eq_dec tid1 tid); subst.
  rewrite <- beq_nat_refl in *.
  destruct (Nat.eq_dec tid2 tid); subst. contradiction.
  apply Nat.eqb_neq in n. rewrite n in *. auto.
  apply Nat.eqb_neq in n. rewrite n in *. 
  destruct (Nat.eq_dec tid2 tid); subst.
  rewrite <- beq_nat_refl in *. auto.
  apply Nat.eqb_neq in n0. rewrite n0 in *. auto.
  apply sto_trace_cons in ST; apply IHt0 in ST.
  simpl in *.
  destruct (Nat.eq_dec tid1 tid); subst.
  rewrite <- beq_nat_refl in *. rewrite ST. auto.
  apply Nat.eqb_neq in n. rewrite n in *. auto.
  auto. auto.
Qed.

Lemma swaps_does_not_reorder num:
  forall t, committed_unconflicted_sto_trace t
  -> forall tid tid0, filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (swaps t tid0 num).
Proof.
  induction num;
  intros t CUST tid tid0.
  simpl; auto.
  simpl.
  assert (committed_unconflicted_sto_trace t). auto.
  apply swap1_preserve_cust with (tid:= tid0) in H.
  apply IHnum with (tid:= tid) (tid0:= tid0) in H.
  apply swap1_does_not_reorder with (tid:= tid) (tid0:= tid0) in CUST.
  rewrite CUST. auto.
Qed.

Lemma create_serialized_trace_does_not_reorder_strong l:
  forall t, committed_unconflicted_sto_trace t
  -> forall tid, filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (create_serialized_trace t l).
Proof.
  induction l;
  intros t CUST tid.
  simpl; auto.
  simpl.
  assert (committed_unconflicted_sto_trace t). auto.
  apply swaps_preserve_cust with (num:= (length t * length t)) (tid:= a) in H.
  apply IHl with (tid:= tid) in H.
  rewrite <- H.
  apply swaps_does_not_reorder with (num:= (length t * length t)) (tid:= tid) (tid0:= a) in CUST.
  auto.
Qed.
(******************************************)
Theorem create_serialized_trace_does_not_reorder t:
  committed_unconflicted_sto_trace t
  -> forall tid, filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (create_serialized_trace t (seq_list t)).
Proof.
  intros CUST tid.
  apply create_serialized_trace_does_not_reorder_strong with (l:= seq_list t) (tid:= tid) in CUST. auto.
Qed.
(******************************************)

Inductive is_serial: trace -> Prop :=
  | serial_constructor: forall t,
      committed_unconflicted_sto_trace t
      -> (forall tid, In tid (seq_list t) -> swap1 t tid = t)
      -> is_serial t.

Lemma is_serial_trace_is_sto_trace t:
  is_serial t
  -> sto_trace t.
Proof.
  intros IS; induction IS; induction H; simpl; auto.
Qed.

Lemma perm_serial_trace_cust t :
  is_serial t
  -> (exists t', committed_unconflicted_sto_trace t'-> Permutation t t').
Proof.
  intros IS.
  induction IS.
  exists t.
  intros.
  auto.
Qed.

Lemma swap1_not_change_length tid:
  forall t, length (swap1 t tid) = length t.
Proof.
  intros.
  functional induction (swap1 t tid); simpl; auto.
Qed.

Lemma swaps_not_change_length tid l:
  forall t, length (swaps t tid l) = length t.
Proof. 
  induction l; intros t.
  simpl. auto.
  simpl. 
  assert (length (swaps (swap1 t tid) tid l) = length (swap1 t tid)).
  apply IHl with (t := (swap1 t tid)).
  rewrite swap1_not_change_length in H; auto.
Qed.

Lemma create_with_swaps_tid_no_swap sl:
  forall t tid, committed_unconflicted_sto_trace t
  -> swap1 (create_serialized_trace (swaps t tid (length t * length t)) sl) tid = create_serialized_trace (swaps t tid (length t * length t)) sl.
Proof.
  induction sl; intros t tid CUST.
  simpl.
  assert (swap1 (swaps t tid (length t * length t)) tid = swaps t tid (length t * length t)). admit. auto.
  simpl.
  assert (length (swaps t tid (length t * length t)) = length t).
  apply swaps_not_change_length with (l:= (length t * length t)).
  rewrite H.
  apply swaps_preserve_cust with (num:= (length t * length t)) (tid:= tid) in CUST; auto.
  apply IHsl with (tid0:= tid) in CUST; auto. 
  rewrite H in CUST.
  destruct (Nat.eq_dec tid a); subst; auto.
Admitted.

Lemma create_serial_trace_no_swap_strong tid sl:
  forall t, committed_unconflicted_sto_trace t
  -> In tid sl 
  -> swap1 (create_serialized_trace t sl) tid = create_serialized_trace t sl.
Proof.
  induction sl;
  intros t CUST IN. 
  simpl in *; inversion IN.
  simpl in *. 
  destruct IN; subst.
  apply create_with_swaps_tid_no_swap; auto.
  apply swaps_preserve_cust with (num:= (length t * length t)) (tid:= a) in CUST.
  apply IHsl in CUST; auto.
Qed.

Lemma create_serial_trace_no_swap tid:
  forall t, committed_unconflicted_sto_trace t
  -> In tid (seq_list t)
  -> swap1 (create_serialized_trace t (seq_list t)) tid = create_serialized_trace t (seq_list t).
Proof.
  intros.
  apply create_serial_trace_no_swap_strong with (sl:= seq_list t); auto.
Qed.

Lemma trace_seqlist_seqpoint t tid:
  In (tid, seq_point) t
  -> In tid (seq_list t).
Proof.
  intros H.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; simpl.
  left. auto.
  right. apply IHl. apply in_inv in H. destruct H.
  inversion H. apply Nat.eq_sym in H1. contradiction. auto.
  destruct _x. destruct a; simpl in H; destruct H; try inversion H; auto. inversion y.
Qed.

Lemma trace_seqlist_seqpoint_rev t tid:
  In tid (seq_list t)
  -> In (tid, seq_point) t.
Proof.
  intros.
  functional induction seq_list t.
  inversion H.
  destruct (Nat.eq_dec tid tid0); subst; simpl; simpl in H. left. auto.
  destruct H. apply eq_sym in H. congruence. apply IHl in H. right. auto.
  destruct _x. destruct a; simpl in *; auto.
Qed.

Lemma seq_list_not_change t tid:
  committed_unconflicted_sto_trace t
  -> In tid (seq_list (create_serialized_trace t (seq_list t)))
  -> In tid (seq_list t).
Proof.
  intros.
  assert (committed_unconflicted_sto_trace t); auto.
  apply create_serialized_trace_does_not_reorder with (tid:= tid) in H.
  apply trace_seqlist_seqpoint_rev in H0.
  apply trace_seqlist_seqpoint.
  Search (filter).
  assert ((fun pr : nat * action => fst pr =? tid) (tid, seq_point) = true). cbn. apply Nat.eqb_refl.
  assert (In (tid, seq_point) (create_serialized_trace t (seq_list t)) /\ (fun pr : nat * action => fst pr =? tid) (tid, seq_point) = true). split; auto.
  apply filter_In in H3; auto.
  rewrite <- H in H3.
  apply filter_In in H3; destruct H3; auto.
Qed.

(******************************************)
Theorem create_serial_trace_is_serial t:
  committed_unconflicted_sto_trace t
  -> is_serial (create_serialized_trace t (seq_list t)).
Proof.
  intros CUST.
  assert (committed_unconflicted_sto_trace t); auto.
  apply serial_constructor.
  apply create_serial_trace_is_cust; auto.
  intros.
  apply create_serial_trace_no_swap with (tid := tid0) in H.
  auto.
  apply seq_list_not_change in H0; auto.
Qed.
(******************************************)



Fixpoint remove_tid tid t: trace :=
  match t with
  | (tid', a) :: t' =>
    if Nat.eq_dec tid tid'
    then remove_tid tid t'
    else (tid', a) :: (remove_tid tid t')
  | [] => []
  end.

Fixpoint remove_noncommitted t tidlist: trace :=
  match tidlist with
  | [] => t
  | tid :: tail => remove_noncommitted (remove_tid tid t) tail
  end.

Definition noncommitted tid t: Prop:=
  trace_tid_phase tid t <> 4.

Fixpoint uncommitted_tids (t t' : trace) : list nat :=
  match t with
  | [] => []
  | (tid, _) :: tail => if (trace_tid_phase tid t' =? 4)
                        then uncommitted_tids tail t'
                        else tid :: (uncommitted_tids tail t')
 end.

Fixpoint uncommitted_tids2 (t: trace) (sl: list nat) : list nat :=
  match sl with
  | [] => []
  | head :: tail => if (trace_tid_phase head t =? 4)
                        then uncommitted_tids2 t tail
                        else head :: (uncommitted_tids2 t tail)
 end.
Fixpoint filter_uncommitted t good : trace :=
  match t with
  | [] => []
  | (tid, a) :: t' => if In_bool tid good || (action_phase a =? 4)
                      then (tid, a) :: filter_uncommitted t' (tid :: good)
                      else filter_uncommitted t' good
  end.

Lemma tid_nonzero_in_remove_tid t tid tid' a: 
  sto_trace t ->
  tid <> tid' ->
  In (tid, a) (remove_tid tid' t) ->
  tid > 0.
Proof.
  intros.
  induction t; simpl in *. inversion H1.
  destruct a0.
  destruct (Nat.eq_dec tid' t0).
  apply sto_trace_cons in H. auto.
  simpl in H1. destruct H1.
  inversion H1; subst.
  assert (In (tid, a) ((tid, a)::t)). simpl; auto.
  apply tid_nonzero in H2; auto. 
  apply sto_trace_cons in H. auto.
Qed.

Lemma remove_tid_not_change_phase tid tid' t:
  tid <> tid'
  -> trace_tid_phase tid t = trace_tid_phase tid (remove_tid tid' t).
Proof.
  intros.
  induction t.
  simpl. auto.
  simpl. destruct a.
  destruct (Nat.eq_dec tid n); destruct (Nat.eq_dec tid' n); subst; try contradiction.
  simpl in *.
  destruct (Nat.eq_dec n n); try contradiction. auto.
  auto.
  simpl in *.
  destruct (Nat.eq_dec tid n); try contradiction. auto.
Qed.

Lemma remove_tid_not_have_lock tid t:
  sto_trace t
  -> locked_by t 0 = 0 \/ locked_by t 0 = tid
  -> locked_by (remove_tid tid t) 0 = 0.
Proof.
  intros.
  assert (sto_trace t); auto.
  induction H; simpl; auto.
  simpl in H0.
  all: destruct (Nat.eq_dec tid tid0); auto.
  simpl in H0.
  assert (tid0 > 0).
  assert (In (tid0, lock_write_item) ((tid0, lock_write_item) :: t)). simpl; auto.
  apply tid_nonzero in H5; auto.
  destruct H0; try omega.
  rewrite e in *.
  assert (locked_by t 0 = 0 \/ locked_by t 0 = tid0). auto. auto.
  simpl in H0.
  rewrite e in *.
  assert (locked_by t 0 = 0 \/ locked_by t 0 = tid0). auto. auto.
Qed.

Lemma remove_tid_not_change_lock t tid':
  sto_trace t -> 
  locked_by t 0 <> tid'
  -> locked_by (remove_tid tid' t) 0 = locked_by t 0.
Proof.
  intros.
  induction H; simpl; auto.
  all: destruct (Nat.eq_dec tid' tid0). 
  all: try rewrite e in *; simpl in *; auto. 
  contradiction.
  apply remove_tid_not_have_lock with (tid0:= tid0) in H2; auto.
  apply remove_tid_not_have_lock with (tid0:= tid0) in H3; auto.
Qed.

Lemma remove_tid_not_change_previous_lock tid tid' t:
  sto_trace t
  -> tid' <> tid
  -> locked_by t tid = tid
  -> locked_by (remove_tid tid' t) tid = tid.
Proof.
  intros.
  induction H; simpl in *; auto.
  all: destruct (Nat.eq_dec tid' tid0); auto.
  rewrite e in *. contradiction.
  rewrite e in *.
  assert (locked_by t 0 = 0 \/ locked_by t 0 = tid0). auto.
  apply remove_tid_not_have_lock in H4; auto.
  { 
    clear H H2 H1 IHsto_trace e.
    induction H3; simpl in *; auto.
    all: destruct (Nat.eq_dec tid0 tid1); auto.
    apply tid_nonzero with (tid0:= tid1) in H1; auto.
    simpl in H4. rewrite H4 in *; omega.
  }
  rewrite e in *.
  assert (locked_by t 0 = 0 \/ locked_by t 0 = tid0). auto.
  apply remove_tid_not_have_lock in H5; auto.
  { 
    clear H H2 H1 H3 IHsto_trace e.
    induction H4; simpl in *; auto.
    all: destruct (Nat.eq_dec tid0 tid1); auto.
    apply tid_nonzero with (tid0:= tid1) in H1; auto.
    simpl in H5. rewrite H5 in *; omega.
  }
Qed.

Lemma remove_tid_not_change_previous_lock2 tid tid' t:
  sto_trace t
  -> tid <> tid'
  -> tid > 0
  -> locked_by t 0 <> tid
  -> locked_by (remove_tid tid' t) 0 <> tid.
Proof.
  intros.
  induction H; simpl in *; auto.
  all: destruct (Nat.eq_dec tid' tid0); auto.
  rewrite H4 in IHsto_trace. auto.
  all: rewrite e in *; rewrite H3 in IHsto_trace; auto.
Qed.

Lemma remove_tid_not_change_write_version t tid':
  sto_trace t
  -> trace_tid_phase tid' t <> 4
  -> trace_write_version t = trace_write_version (remove_tid tid' t).
Proof.
  intros.
  induction H; simpl in *; auto.
  all: destruct (Nat.eq_dec tid' tid0); simpl.
  rewrite e in *. rewrite H1 in IHsto_trace. auto. auto.
  all: try rewrite e in *; try rewrite H in IHsto_trace; auto; auto.
  omega.
Qed.
  
Lemma remove_tid_not_change_in tid action t tid':
  tid <> tid' ->
  In (tid, action) t -> In (tid, action) (remove_tid tid' t).
Proof.
  intros.
  induction t; simpl; auto.
  destruct a.
  destruct (Nat.eq_dec tid' n).
  simpl in H0. destruct H0. inversion H0. rewrite e in *. rewrite H2 in *. contradiction. auto.
  simpl in *. destruct H0; auto.
Qed.

Lemma remove_tid_not_change_in_rev tid action t tid':
  tid <> tid' ->
  In (tid, action) (remove_tid tid' t) -> In (tid, action) t.
Proof.
  intros.
  induction t; simpl; auto.
  destruct a. simpl in *.
  destruct (Nat.eq_dec tid' n); simpl in *; auto.
  destruct H0; auto.
Qed.


Lemma remove_tid_not_change_last_write tid tid' t:
  sto_trace t 
  -> trace_tid_phase tid' t <> 4 
  -> tid <> tid' 
  -> trace_tid_last_write tid t = trace_tid_last_write tid (remove_tid tid' t).
Proof.
  intros.
  induction H; simpl in *; auto.
  all: destruct (Nat.eq_dec tid tid0); try contradiction.
  all: destruct (Nat.eq_dec tid' tid0); try contradiction.
  all: try rewrite e in *; try rewrite e0 in *; try contradiction.
  all: simpl in *; try destruct (Nat.eq_dec tid0 tid0); try contradiction; auto.
  all: try destruct (Nat.eq_dec tid tid0); try contradiction; auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H2; omega. auto.
  all: assert (trace_tid_phase tid0 t <> 4); try rewrite H; try omega; auto.
Qed.

Lemma remove_one_noncommitted_preserve_st tid t:
  sto_trace t
  -> noncommitted tid t
  -> sto_trace (remove_tid tid t).
Proof.  
  intros. assert (sto_trace t) as COPY; auto.
  induction H; simpl; auto; 
  apply sto_trace_cons in COPY.
  all: destruct (Nat.eq_dec tid tid0); subst.
  all: unfold noncommitted in *; auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H1. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H1; auto. auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  apply remove_tid_not_have_lock with (tid0:= tid) in H2; auto.
  rewrite remove_tid_not_change_write_version with (tid' := tid); auto. auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  apply remove_tid_not_have_lock with (tid0:= tid) in H3; auto.
  apply remove_tid_not_change_in with (tid':= tid) in H1; auto.
  apply lock_write_item_step with (tid0:= tid0) (v:= v) in H0; auto. auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  assert (forall v : value,
     In (tid0, write_item v) (remove_tid tid t) -> In (tid0, lock_write_item) (remove_tid tid t)).
  intros.
  apply remove_tid_not_change_in_rev in H4; auto. apply H1 in H4.
  apply remove_tid_not_change_in with (tid' := tid) in H4; auto.
  apply seq_point_step with (tid:= tid0) in H0; auto. auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  apply remove_tid_not_change_previous_lock with (tid':= tid) in H1; auto.
  rewrite remove_tid_not_change_write_version with (tid':= tid); auto. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H1; auto.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto. auto.
  remember (locked_by t 0) as tid0.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  remember (locked_by t 0) as tid0.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid':= tid) in H; auto.
  apply Nat.eq_sym in Heqtid0.
  assert (locked_by t 0 = tid0). auto.
  rewrite <- remove_tid_not_change_lock with (tid' := tid) in Heqtid0; auto. rewrite H3. auto. auto.
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  assert (forall vers : version,
     In (tid0, read_item vers) (remove_tid tid t) -> In (tid0, validate_read_item vers) (remove_tid tid t)).
  intros. apply remove_tid_not_change_in_rev in H5; auto. apply H1 in H5.
  apply remove_tid_not_change_in with (tid' := tid) in H5; auto.
  assert (forall vers : version,
     In (tid0, validate_read_item vers) (remove_tid tid t) -> In (tid0, read_item vers) (remove_tid tid t)).
  intros. apply remove_tid_not_change_in_rev in H6; auto. apply H2 in H6.
  apply remove_tid_not_change_in with (tid' := tid) in H6; auto.
  apply commit_txn_step with (tid:= tid0) in H0; auto. auto.
  remember (locked_by t 0) as tid0. 
  simpl in H0. destruct (Nat.eq_dec tid0 tid0); try contradiction.
  remember (locked_by t 0) as tid0. 
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  rewrite remove_tid_not_change_write_version with (tid':= tid); auto.
  rewrite remove_tid_not_change_last_write with (tid':= tid) in H2; auto.
  apply Nat.eq_sym in Heqtid0.
  assert (locked_by t 0 = tid0). auto.
  rewrite <- remove_tid_not_change_lock with (tid' := tid) in Heqtid0; auto.
  apply complete_write_item_step with (tid0:= tid0) (val:= val) in H0; auto.
  rewrite H4. auto. auto.
  simpl in H0. destruct (Nat.eq_dec tid0 tid0); try contradiction.
  simpl in H0. destruct (Nat.eq_dec tid tid0); try contradiction.
  assert (trace_tid_phase tid t <> 4). auto.
  apply IHsto_trace in H0.
  assert (tid0 > 0). apply trace_phase_nonzero with (tid:= tid0) in H2; auto. rewrite H. omega.
  rewrite remove_tid_not_change_phase with (tid' := tid) in H; auto.
  apply remove_tid_not_change_previous_lock2 with (tid':= tid) in H1; auto. auto.
Qed.

Lemma uncommitted_tid_list_is_noncommitted_tids_strong tid t l:
  In tid (uncommitted_tids2 t l)
  -> noncommitted tid t.
Proof.
  intros.
  induction l.
  simpl in *; inversion H.
  simpl in *.
  unfold noncommitted in *.
  destruct (Nat.eq_dec (trace_tid_phase a t) 4).
  apply (Nat.eqb_eq) in e. rewrite e in *.
  apply IHl in H. auto.
  apply (Nat.eqb_neq) in n. rewrite n in *.
  simpl in H. destruct H; subst.
  apply (Nat.eqb_neq) in n. auto.
  apply IHl in H. auto.
Qed.

Lemma uncommitted_tid_list_is_noncommitted_tids tid t:
  In tid (uncommitted_tids2 t (tid_list t))
  -> noncommitted tid t.
Proof.
  intros.
  apply uncommitted_tid_list_is_noncommitted_tids_strong with (l:= tid_list t). auto.
Qed.

Lemma uncommitted_tid_list_is_noncommitted_tids_rev_strong tid t l:
  noncommitted tid t
  -> In tid l
  -> In tid (uncommitted_tids2 t l).
Proof.
  intros.
  induction l.
  simpl in *. auto.
  simpl in *. 
  destruct H0.
  destruct (Nat.eq_dec (trace_tid_phase a t) 4).
  subst. unfold noncommitted in H. contradiction.
  apply Nat.eqb_neq in n. rewrite n.
  simpl. auto.
  destruct (Nat.eq_dec (trace_tid_phase a t) 4).
  apply Nat.eqb_eq in e. rewrite e. auto.
  apply Nat.eqb_neq in n. rewrite n. simpl. auto.
Qed.

Lemma uncommitted_tid_list_is_noncommitted_tids_rev tid t:
  noncommitted tid t
  -> In tid (tid_list t)
  -> In tid (uncommitted_tids2 t (tid_list t)).
Proof.
  intros.
  apply uncommitted_tid_list_is_noncommitted_tids_rev_strong; auto.
Qed.

Lemma remove_tid_is_noncommitted tid t:
  noncommitted tid (remove_tid tid t).
Proof.
  unfold noncommitted.
  induction t.
  simpl. omega.
  simpl.
  destruct a.
  destruct (Nat.eq_dec tid n); auto.
  simpl.
  destruct (Nat.eq_dec tid n); try contradiction. auto.
Qed.
  
Lemma remove_tid_preserve_noncommitted tid tid' t:
  noncommitted tid t
  -> noncommitted tid (remove_tid tid' t).
Proof.
  intros.
  unfold noncommitted in *.
  induction t.
  simpl. omega.
  simpl.
  destruct a.
  destruct (Nat.eq_dec tid' n).
  destruct (Nat.eq_dec tid n); subst.
  apply remove_tid_is_noncommitted.
  simpl in H. destruct (Nat.eq_dec tid n); try contradiction. auto.
  simpl in *.
  destruct (Nat.eq_dec tid n); auto.
Qed.

Lemma remove_tid_preserve_noncommitted_equal tid tid' t:
  tid <> tid' ->
  noncommitted tid t = noncommitted tid (remove_tid tid' t).
Proof.
  intros.
  unfold noncommitted in *.
  induction t.
  simpl. auto.
  simpl.
  destruct a.
  destruct (Nat.eq_dec tid n); subst.
  destruct (Nat.eq_dec tid' n); subst.
  all: try contradiction.
  simpl.
  destruct (Nat.eq_dec n n); try contradiction. auto.
  destruct (Nat.eq_dec tid' n); auto.
  simpl.
  destruct (Nat.eq_dec tid n); try contradiction. auto.
Qed.

Lemma remove_all_noncommitted_preserve_st ul:
  forall t, sto_trace t
  -> (forall tid, In tid ul -> noncommitted tid t)
  -> sto_trace (remove_noncommitted t ul).
Proof.
  induction ul;
  intros t ST I.
  simpl; auto.
  simpl. 
  apply IHul.
  apply remove_one_noncommitted_preserve_st with (tid:= a) in ST. auto.
  simpl in I.
  assert (In a (a::ul) -> noncommitted a t). apply I.
  simpl in H. auto.
  intros.
  assert (In tid0 (a :: ul)). simpl. auto.
  apply I in H0.
  apply remove_tid_preserve_noncommitted. auto.
Qed.


Lemma from_sto_trace_to_cust t:
  sto_trace t
  -> (forall tid, trace_tid_phase tid t > 0
      -> ~ noncommitted tid t)
  -> committed_unconflicted_sto_trace t.
Proof.
  intros.
  apply construct_cust.
  auto.
  intros.
  apply H0 in H1.
  unfold noncommitted in H1.
  intuition.
Qed.

Lemma tid_in_remove_tid_not_tid tid x tid' t:
  In (tid, x) (remove_tid tid' t) 
  -> tid <> tid'.
Proof.
  intros.
  induction t.
  simpl in H. inversion H.
  destruct a.
  simpl in H.
  destruct (Nat.eq_dec tid' n). auto.
  simpl in H.
  destruct H.
  inversion H. rewrite H1 in n0.
  apply Nat.neq_sym in n0. auto. auto.
Qed.

Lemma tid_in_remove_tid_is_in_t tid x a t:
  In (tid, x) (remove_tid a t)
  -> In (tid, x) t.
Proof.
  intros.
  induction t.
  simpl in *. auto.
  simpl in *.
  destruct a0.
  destruct (Nat.eq_dec a n); subst. auto.
  simpl in H. 
  destruct H; auto.
Qed.

Lemma tid_in_remove_noncommitted_not_in_uncommitted tid x ul:
  forall t, In (tid, x) (remove_noncommitted t ul)
  -> In (tid, x) t /\ ~ In tid ul.
Proof.
  induction ul;
  intros t INt.
  simpl in *. auto.
  simpl in *.
  assert (In (tid, x) (remove_noncommitted (remove_tid a t) ul)). auto.
  apply IHul in INt.
  split.
  destruct INt; auto.
  apply tid_in_remove_tid_is_in_t in H0. auto.
  destruct INt.
  apply and_not_or. split; auto.
  apply tid_in_remove_tid_not_tid in H0; auto.
Qed.

Lemma not_in_uncommitted_tids_is_phase4 tid t:
  In tid (tid_list t)
  -> ~ In tid (uncommitted_tids2 t (tid_list t))
  -> ~ noncommitted tid t.
Proof.
  intros.
  intuition.
  apply uncommitted_tid_list_is_noncommitted_tids_rev in H1; auto.
Qed.

Lemma noncommitted_preserve tid ul:
  forall t, ~ noncommitted tid t
  -> ~ In tid ul
  -> ~ noncommitted tid (remove_noncommitted t ul).
Proof.
  induction ul.
  simpl; auto.
  simpl in *.
  intros.
  apply not_or_and in H0. destruct H0.
  assert (~ noncommitted tid (remove_tid a t)).
  rewrite remove_tid_preserve_noncommitted_equal with (tid':= a) in H. auto. auto. apply IHul in H2; auto.
Qed.

Lemma trace_tid_phase_preserve_same_remove_tid tid a t:
  trace_tid_phase tid (remove_tid a t) >0
  -> trace_tid_phase tid t > 0.
Proof.
  intros.
  apply trace_phase_in in H.
  destruct H.
  assert (tid <> a).
  { intuition. subst. 
    induction t. simpl in *. auto.
    destruct a0. simpl in *.
    destruct (Nat.eq_dec a n). auto.
    simpl in H. destruct H. 
    inversion H. rewrite H1 in n0. contradiction. auto.
  }
  induction t.
  simpl in *. inversion H.
  destruct a0 in *.
  simpl in *.
  destruct (Nat.eq_dec a n); subst.
  destruct (Nat.eq_dec tid n); try contradiction. auto.
  destruct (Nat.eq_dec tid n).
  destruct a0; simpl; omega. 
  simpl in H. destruct H. inversion H. 
  rewrite H2 in n1. contradiction. auto.
Qed.

Lemma trace_tid_phase_preserve_same_remove_noncommitted tid ul:
  forall t, trace_tid_phase tid (remove_noncommitted t ul) > 0
  -> trace_tid_phase tid t >0.
Proof.
  induction ul.
  simpl in *. auto.
  intros.
  simpl in *. apply IHul in H.
  apply trace_tid_phase_preserve_same_remove_tid in H. auto.
Qed.

(******************************************)
Theorem remove_noncommitted_sto_trace_is_cust t :
  sto_trace t
  -> committed_unconflicted_sto_trace (remove_noncommitted t (uncommitted_tids2 t (tid_list t))).
Proof.
  intros ST.
  assert (sto_trace t) as COPY. auto.
  apply remove_all_noncommitted_preserve_st with (ul:= (uncommitted_tids2 t (tid_list t))) in ST.
  apply from_sto_trace_to_cust. auto.
  intros.
  intuition.
  assert (trace_tid_phase tid0 (remove_noncommitted t (uncommitted_tids2 t (tid_list t))) > 0) as H1. auto.
  apply trace_tid_phase_preserve_same_remove_noncommitted in H1; auto.
  apply trace_phase_in_tid_list in H1; auto.
  apply trace_phase_in in H; destruct H.
  apply tid_in_remove_noncommitted_not_in_uncommitted in H. destruct H.
  apply not_in_uncommitted_tids_is_phase4 in H1; auto.
  apply noncommitted_preserve with (ul:= (uncommitted_tids2 t (tid_list t))) in H1; auto.
  intros. apply uncommitted_tid_list_is_noncommitted_tids. auto.
Qed.
(******************************************)

Lemma remove_one_noncommitted_does_not_reorder t tid' tid:
  sto_trace t
  -> noncommitted tid' t
  -> tid <> tid'
  -> filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (remove_tid tid' t).
Proof.
  intros.
  induction H.
  simpl. auto.
  all: unfold noncommitted in *; simpl in H0; destruct (Nat.eq_dec tid' tid0); try apply IHsto_trace in H0.
  simpl. rewrite e in *.
  destruct (Nat.eq_dec tid tid0); try contradiction.
  apply Nat.neq_sym in n. apply Nat.eqb_neq in n. rewrite n.
  destruct (Nat.eq_dec tid0 tid0); try contradiction.
  assert (trace_tid_phase tid0 t <> 4). rewrite H2. omega. auto.
  all: simpl; destruct (Nat.eq_dec tid' tid0); try contradiction.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). intuition. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  rewrite e0 in *.
  destruct (Nat.eq_dec tid0 tid); try apply Nat.eq_sym in e1; try contradiction.
  apply Nat.eqb_neq in n. rewrite n. 
  assert (trace_tid_phase tid0 t <> 4). rewrite H. omega. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  destruct (Nat.eq_dec tid0 tid); try contradiction.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
  destruct (Nat.eq_dec tid0 tid). apply Nat.eqb_eq in e. rewrite e.
  simpl. rewrite e. rewrite H0. auto.
  apply Nat.eqb_neq in n1. rewrite n1.
  simpl. rewrite n1. auto.
Qed.
  

Lemma remove_noncommitted_does_not_reorder_strong l tid':
  forall t, sto_trace t
  -> (forall tid, In tid l -> noncommitted tid t)
  -> ~ In tid' l
  -> filter (fun pr => fst pr =? tid') t = filter (fun pr => fst pr =? tid') (remove_noncommitted t l).
Proof.
  induction l;
  intros t ST I.
  simpl; auto.
  simpl.
  assert (sto_trace t). auto.
  apply remove_one_noncommitted_preserve_st with (tid:= a) in H.
  assert (In a (a::l) -> noncommitted a t). intros. auto.
  assert (In a (a::l)). simpl. auto. apply H0 in H1.
  intros.
  apply not_or_and in H2. destruct H2.
  apply remove_one_noncommitted_does_not_reorder with (tid := tid') (tid' := a) in ST; auto. 
  apply IHl in H; auto.
  rewrite <- ST in H. auto.
  intros.
  assert (In tid0 (a :: l)). simpl; auto.
  apply I in H5.
  apply remove_tid_preserve_noncommitted with (tid' := a) in H5.
  auto. 
  assert (In a (a::l) -> noncommitted a t). intros. auto.
  assert (In a (a::l)). simpl. auto. apply H0 in H1. auto.
Qed.

(******************************************)
Theorem remove_noncommitted_does_not_reorder t tid:
  sto_trace t
  -> ~ In tid  (uncommitted_tids2 t (tid_list t))
  -> filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (remove_noncommitted t (uncommitted_tids2 t (tid_list t))).
Proof.
  intros.
  apply remove_noncommitted_does_not_reorder_strong with (tid' := tid) (l := (uncommitted_tids2 t (tid_list t))) in H; auto.
  intros.
  apply uncommitted_tid_list_is_noncommitted_tids. auto.
Qed.
(******************************************)







