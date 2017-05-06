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
(*|restart_txn: action*)
|commit_txn: action
|complete_write_item: (*value -> action*)version -> action
(*|unlock_write_item: version -> action*)
(*|invalid_write_item: value -> action*)
|commit_done_txn: action.
(*|obtain_global_tid: action.*)
(*sp later than last lock, but must before the first commit*)
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

Fixpoint trace_outstanding_read_list tid t: list nat :=
  match t with
  | (tid', read_item ver) :: t' => 
    if Nat.eq_dec tid tid'
    then trace_outstanding_read_list tid t'
    else tid :: trace_outstanding_read_list tid t'
  | _ :: t' => trace_outstanding_read_list tid t'
  | [] => []
  end.

Definition tid_in_phase_4 (tid: tid) (t: trace): Prop:=
  trace_tid_phase tid t = 4.

Fixpoint no_outstanding_read tid trace: Prop:=
  match trace with
  | [] => True
  | (tid', read_item v) :: tail => 
      if (Nat.eq_dec tid tid')
      then (In (tid, validate_read_item v) tail) /\ (no_outstanding_read tid tail)
      else no_outstanding_read tid tail
  | _ :: tail => no_outstanding_read tid tail
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


Inductive unconflicted_sto_trace : trace -> Prop :=

| uc_empty_step : unconflicted_sto_trace []

| uc_start_txn_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, start_txn)::t)
    -> unconflicted_sto_trace ((tid, start_txn)::t)

| uc_read_item_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, read_item (trace_write_version t)) :: t)
    -> unconflicted_sto_trace ((tid, read_item (trace_write_version t)) :: t)

| uc_write_item_step: forall t tid val,
    unconflicted_sto_trace t
    -> sto_trace ((tid, write_item val) :: t)
    ->unconflicted_sto_trace ((tid, write_item val) :: t)

| uc_try_commit_txn_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, try_commit_txn)::t)
    -> unconflicted_sto_trace ((tid, try_commit_txn)::t)

| uc_lock_write_item_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, lock_write_item) :: t)
    -> (forall tid', tid' <> tid /\ no_outstanding_read tid' t) (*no outstanding read*)
    -> unconflicted_sto_trace ((tid, lock_write_item) :: t)

(*sequential point*)
| uc_seq_point_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, seq_point) :: t)
    -> unconflicted_sto_trace ((tid, seq_point) :: t)

| uc_validate_read_item_step: forall t tid vers,
    unconflicted_sto_trace t
    -> sto_trace ((tid, validate_read_item vers) :: t)
    -> unconflicted_sto_trace ((tid, validate_read_item vers) :: t)

| uc_commit_txn_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, commit_txn) :: t)
    -> unconflicted_sto_trace ((tid, commit_txn) :: t)

| uc_complete_write_item_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, complete_write_item (S (trace_write_version t))) :: t)
    -> unconflicted_sto_trace ((tid, complete_write_item (S (trace_write_version t))) :: t)

| uc_commit_done_step: forall t tid,
    unconflicted_sto_trace t
    -> sto_trace ((tid, commit_done_txn) :: t)
    -> unconflicted_sto_trace ((tid, commit_done_txn) :: t).
Hint Constructors unconflicted_sto_trace.

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

Fixpoint swap_once tid (t:trace) :=
  match t with
  | (tid1, a1) :: (tid2, a2) :: t' =>
    (* maybe swap but only swap if equals tid *)
      if Nat.eq_dec tid1 tid2 
        then (tid1, a1)::(tid2, a2)::(swap_once tid t')
      else if (tid =? tid1) && (3 <=? action_phase a1) && (is_not_seq_point a1)
        then (tid2, a2)::(tid1, a1)::(swap_once tid t')
      else if (tid =? tid2) && (action_phase a2 <? 3)
        then (tid2, a2)::(tid1, a1)::(swap_once tid t')
      else (tid1, a1)::(tid2, a2)::(swap_once tid t')
  | _ => t
  end.

Inductive is_serial: trace -> Prop :=
  | serial_constructor: forall t,
      committed_unconflicted_sto_trace t
      -> (forall tid, swap_once tid t = t)
      -> is_serial t.

Lemma unconflicted_is_sto_trace t:
  unconflicted_sto_trace t
  -> sto_trace t.
Proof.
  intros ST; induction ST; auto.
Qed.

(******************************************)
Theorem cust_is_sto_trace t:
  committed_unconflicted_sto_trace t
  -> sto_trace t.
Proof.
  intros CUST; induction CUST; simpl; auto.
Qed.
(******************************************)

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

Function swap_action_tid (tid: tid) (t:trace) {measure length t} : trace :=
  match t with
  | [] => []
  | (tid1, action1) :: tail' =>
    match tail' with
    | [] => [(tid1, action1)]
    | (tid2, action2) :: tail =>
      if tid1 =? tid2
      then
          (tid1, action1) :: swap_action_tid tid ((tid2, action2) :: tail)
      else
          if tid1 =? tid
          then
               if (3 <=? action_phase action1) && (is_not_seq_point action1)
               then 
                    (tid2, action2) :: swap_action_tid tid ((tid1, action1) :: tail)
               else 
                    (tid1, action1) :: swap_action_tid tid ((tid2, action2) :: tail)
          else
               if tid2 =? tid
               then if action_phase action2 <? 3
                    then 
                         (tid2, action2) :: swap_action_tid tid ((tid1, action1) :: tail)
                    else 
                         (tid1, action1) :: swap_action_tid tid ((tid2, action2) :: tail)
               else 
                    (tid1, action1) :: swap_action_tid tid ((tid2, action2) :: tail)
    end
  end.
Proof.
  all: intros; simpl; auto.
Defined.
  

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

Function create_serialized_trace3 (t: trace) (sl : list nat):=
  match sl with
  | head :: tail => create_serialized_trace3 (swaps t head ((length t) * (length t))) tail
  | [] => t
  end.


Function swap_action_tid_repeat (tid: tid) (t : trace) (n : nat) : trace :=
  match n with
  | 0 => t
  | S m => swap_action_tid_repeat tid (swap_action_tid tid t) m
  end.

Function create_serialized_trace2 (t : trace) (seq_list : list tid) : trace :=
  match seq_list with
  | [] => t
  | head :: tail => create_serialized_trace2 (swap_action_tid_repeat head t (length t)) tail
end.

Lemma create_serial_trace_no_swap t:
  committed_unconflicted_sto_trace t
  -> (forall tid, (swap_once tid (create_serialized_trace3 t (seq_list t)) = create_serialized_trace3 t (seq_list t))).
Proof.
  intros CUST.
  destruct create_serialized_trace3. simpl. auto.
Admitted.

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
  assert (In (tid1, complete_write_item v) ((tid1, complete_write_item v)
        :: (tid2, complete_write_item v0) :: tail')). simpl. auto.
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

Lemma sto_trace_swap_app tid1 tid2 a1 a2 t t':
  sto_trace ((tid2, a2) :: (tid1, a1) :: t)
  -> sto_trace (t' ++ (tid1, a1) :: (tid2, a2) :: t)
  -> action_phase a1 <> 6
  -> action_phase a2 <> 6
  -> 3 <= action_phase a1
  -> a1 <> seq_point
  -> sto_trace (t' ++ (tid2, a2) :: (tid1, a1) :: t).
Admitted.

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
  assert (trace_tid_phase tid2 ((tid1, validate_read_item vers) :: tail') = 0). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in _x; try contradiction; auto.
  apply start_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  simpl in H5. simpl in H6. apply sto_trace_cons in H7.
  apply validate_read_item_step with (tid0:= tid1) (vers:= vers) in H7; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 1). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (locked_by ((tid1, start_txn) :: tail') 0 = 0). simpl; auto.
  assert (trace_write_version tail' = trace_write_version ((tid1, start_txn) :: tail')). simpl; auto. rewrite H15.
  apply read_item_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 1). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  apply write_item_step with (tid:= tid2) (val:= val) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 1). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  apply try_commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 2). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (locked_by ((tid1, start_txn) :: tail') 0 = 0). simpl; auto.
  assert (In (tid2, write_item v) ((tid1, start_txn) :: tail')); simpl; auto.
  apply lock_write_item_step with (tid0:= tid2) (v:= v) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 2). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (forall v : value,
      In (tid2, write_item v) ((tid1, start_txn) :: tail') -> In (tid2, lock_write_item) ((tid1, start_txn) :: tail')). 
  intros. simpl in H14. destruct H14. inversion H14; try contradiction.
  apply H11 in H14. simpl. auto.
  apply seq_point_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 3). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (locked_by ((tid1, start_txn) :: tail') tid2 = tid2). simpl; auto.
  assert (trace_write_version ((tid1, start_txn) :: tail') = vers); simpl; auto.
  apply validate_read_item_step with (tid0:= tid2) (vers:= vers) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
  rewrite <- H8 in NE62. simpl in NE62. omega.
  rewrite <- H8 in NE62. simpl in NE62. omega.
  
  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 3). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (forall vers : version,
      In (tid2, read_item vers) ((tid1, start_txn) :: tail') -> In (tid2, validate_read_item vers) ((tid1, start_txn) :: tail')). 
  intros. simpl in H14. destruct H14. inversion H14; try contradiction.
  apply H11 in H14. simpl. auto.
  apply commit_txn_step with (tid:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 4). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (locked_by ((tid1, start_txn) :: tail') 0 = tid2). simpl; auto.
  assert (trace_tid_last_write tid2 ((tid1, start_txn) :: tail') = Some val). simpl. destruct (Nat.eq_dec tid2 tid1); auto.
  assert (trace_write_version ((tid1, start_txn) :: tail') = (trace_write_version tail')); simpl; auto.
  apply complete_write_item_step with (tid0:= tid2) (val:= val) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.

  assert (trace_tid_phase tid2 ((tid1, start_txn) :: tail') = 4). simpl. destruct (Nat.eq_dec tid2 tid1); try rewrite e in n; try contradiction; auto.
  assert (locked_by ((tid1, start_txn) :: tail') 0 <> tid2). simpl; auto.
  apply commit_done_step with (tid0:= tid2) in H7; auto.
  apply sto_trace_swap_app in H; subst; auto.
  
Admitted.


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
  -> committed_unconflicted_sto_trace (create_serialized_trace3 t l).
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
  -> committed_unconflicted_sto_trace (create_serialized_trace3 t (seq_list t)).
Proof.
  intros CUST.
  apply create_serial_trace_is_cust_strong with (l:= seq_list t). auto.
Qed.
(******************************************)

(******************************************)
Theorem create_serial_trace_is_serial t:
  committed_unconflicted_sto_trace t
  -> is_serial (create_serialized_trace3 t (seq_list t)).
Proof.
  intros CUST.
  assert (committed_unconflicted_sto_trace t); auto.
  apply serial_constructor.
  apply create_serial_trace_is_cust; auto.
  intros.
  apply create_serial_trace_no_swap with (tid := tid0) in H.
  auto.
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
  -> forall tid, filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (create_serialized_trace3 t l).
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
  -> forall tid, filter (fun pr => fst pr =? tid) t = filter (fun pr => fst pr =? tid) (create_serialized_trace3 t (seq_list t)).
Proof.
  intros CUST tid.
  apply create_serialized_trace_does_not_reorder_strong with (l:= seq_list t) (tid:= tid) in CUST. auto.
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
  intros. apply remove_tid_not_change_in_rev in H4; auto. apply H1 in H4.
  apply remove_tid_not_change_in with (tid' := tid) in H4; auto.
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














Lemma perm_cust_serial_trace t :
  committed_unconflicted_sto_trace t
  -> Permutation t (create_serialized_trace2 t (seq_list t)).
Proof.
  intros CUST.
  destruct create_serialized_trace2. simpl; auto.
Admitted.

Lemma serial_trace_is_subset_sto_trace t:
  sto_trace t
  -> (exists t', is_serial t'
    -> (forall tid, filter func t' <> empty
      -> filter func t' = filter func t)).

(*
Check whether an element a is in the list l
*)



Lemma remove_noncommit_phase_same tid tid0 t n:
  sto_trace t
  -> trace_tid_phase tid t = n
  -> tid <> tid0
  -> trace_tid_phase tid (remove_tid tid0 t) = n.
Proof.
  intros ST P NE.
  induction t.
  simpl; auto.
  destruct a. simpl in *.
  destruct (Nat.eq_dec tid0 t0); subst.
  destruct (Nat.eq_dec tid t0); subst; try contradiction.
  apply sto_trace_cons in ST. apply IHt in ST; auto.
  destruct (Nat.eq_dec tid t0); subst.
Admitted.


Lemma remove_noncommit_ok tid t:
  trace_tid_phase tid t <> 4
  -> sto_trace t
  -> sto_trace (remove_tid tid t).
Proof.
  intros LT ST.
  induction ST; simpl; auto.
  destruct (Nat.eq_dec tid tid0); subst; simpl in *.
  assert (trace_tid_phase tid0 t <> 4) as not_equal_4. { rewrite H0. omega. } apply IHST in not_equal_4; auto.
  destruct (Nat.eq_dec tid tid0). contradiction. apply IHST in LT.
  apply start_txn_step with (tid:= tid0) in LT; auto.
  apply remove_noncommit_phase_same with (tid0 := tid) in H0; auto.

  simpl in *.
  destruct (Nat.eq_dec tid tid0); subst.
  assert (trace_tid_phase tid0 t <> 4) as not_equal_4. { rewrite H. omega. } apply IHST in not_equal_4; auto.
  apply IHST in LT.
  
Admitted.

Lemma remove_noncommit_write_version_same tid t:
  sto_trace t
  -> trace_tid_phase tid t <> 4
  -> trace_write_version t = trace_write_version (remove_tid tid t).
Proof.
  intros ST NE.
  induction ST; simpl in *; auto.
  destruct (Nat.eq_dec tid tid0).
Admitted.

Lemma remove_all_noncommit_ok t: (*the same as no_committed_sto_trace_is_sto_trace*)
  sto_trace t
  -> sto_trace (remove_noncommitted t (uncommitted_tids t t)).
Proof.
  intros ST.
  induction ST; simpl; auto.
  all: destruct (Nat.eq_dec tid0 tid0); subst.
{
  assert (1 <> 4) as not_equal; try omega; try apply Nat.eqb_neq in not_equal; simpl.
  destruct (Nat.eq_dec tid0 tid0); subst; simpl.
  
  simpl.
Admitted.


Lemma noncommitted_sto_trace_is_unconflicted t :
  sto_trace t
  -> unconflicted_sto_trace (remove_noncommitted t (uncommitted_tids t t)).
Proof.
  intros ST.
  induction ST; simpl; auto.
Admitted.

Lemma no_committed_sto_trace_is_sto_trace t :
  sto_trace t
  -> sto_trace (remove_noncommitted t (uncommitted_tids t t)).
Proof.
  intros ST; apply noncommitted_sto_trace_is_unconflicted in ST; apply unconflicted_is_sto_trace in ST; auto.
Qed.

Inductive swappable: tid -> action -> tid -> action -> Prop :=
  | after_seq_point: forall (tid1 tid2: tid) (action1 action2: action),
    tid1 <> tid2
    -> 3 <= action_phase action1
    -> action1 <> seq_point
    -> swappable tid1 action1 tid2 action2
  | before_seq_point: forall (tid1 tid2: tid) (action1 action2: action),
    tid1 <> tid2
    -> action_phase action2 < 3
    -> swappable tid1 action1 tid2 action2.
Hint Constructors swappable.

Inductive swapstep1 : relation trace :=
  | swap_step_after_seq_point : forall (tid1 tid2: tid) (action1 action2: action) (t1 t2: trace),
    tid1 <> tid2
    -> 3 <= action_phase action1
    -> action1 <> seq_point
    -> swapstep1 (t1 ++ (tid1, action1) :: (tid2, action2) :: t2) 
              (t1 ++ (tid2, action2) :: (tid1, action1) :: t2)
  | swap_step_before_seq_point: forall (tid1 tid2: tid) (action1 action2: action) (t1 t2: trace),
    tid1 <> tid2
    -> action_phase action2 < 3
    -> swapstep1 (t1 ++ (tid1, action1) :: (tid2, action2) :: t2) 
              (t1 ++ (tid2, action2) :: (tid1, action1) :: t2).

Inductive swapsteps : relation trace :=
  | swap_refl: forall tr1 tr2,
      tr1 = tr2 ->
      swapsteps tr1 tr2
  | swao_trans: forall tr1 tr2 tr3,
      swapsteps tr1 tr2 ->
      swapstep1 tr2 tr3 ->
      swapsteps tr1 tr3.
Hint Constructors swapsteps.

Lemma swappable_swapstep tid1 tid2 action1 action2 t1 t2:
  swappable tid1 action1 tid2 action2
  -> swapstep1 (t1 ++ (tid1, action1) :: (tid2, action2) :: t2)
              (t1 ++ (tid2, action2) :: (tid1, action1) :: t2).
Proof.
  intros SW.
  induction SW; subst; simpl; auto.
  apply swap_step_after_seq_point; auto.
  apply swap_step_before_seq_point; auto.
Qed.

Lemma swapstep_swappable tid1 tid2 action1 action2 t1 t2:
  swapstep1 (t1 ++ (tid1, action1) :: (tid2, action2) :: t2)
              (t1 ++ (tid2, action2) :: (tid1, action1) :: t2)
  -> swappable tid1 action1 tid2 action2.
Proof.
  intros ST.
  inversion ST.
Admitted. (*Unsolved*)

Lemma swap_tid_is_by_swapsteps t tid :
  unconflicted_sto_trace t 
  -> swapsteps t (swap_action_tid tid t).
Proof.
  intros UST.
  induction t.
  simpl. auto.
  destruct a. simpl.
Admitted.

Lemma swap_tid_repeat_is_by_swapsteps t tid:
  unconflicted_sto_trace t
  -> swapsteps t (swap_action_tid_repeat tid t (length t)).
Proof.
Admitted.

Lemma create_serialized_trace_is_by_swapsteps t:
  unconflicted_sto_trace t 
  -> swapsteps t (create_serialized_trace2 t (seq_list t)).
Proof.
  intros UST.
  induction (seq_list t).
  simpl; auto.
  simpl.
  assert (unconflicted_sto_trace (create_serialized_trace t l)). admit.
  remember (create_serialized_trace2 t l) as t'.
  apply swap_tid_repeat_is_by_swapsteps with (tid0:= a) in H.
  
  
  
  
Admitted.

Lemma unconflict_tids_must_be_phase_4 tr tid action:
  unconflicted_sto_trace tr
  -> In (tid, action) tr
  -> trace_tid_phase tid tr = 4.
Proof.
  intros UST IN.
  induction UST.
  now apply H0 in IN.
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

Lemma sto_trace_can_swap tid1 tid2 action1 action2 t:
  sto_trace ((tid1, action1) :: (tid2, action2) :: t)
  -> tid1 <> tid2
  -> action_phase action1 = 4 /\ action_phase action2 = 4
  -> sto_trace ((tid2, action2) :: (tid1, action1) :: t).
Proof.
  intros ST NE AP.
  destruct AP.
  inversion ST. 
  all: try rewrite <- H2 in H; inversion H.
  apply sto_trace_cons in ST.
  inversion ST.
  all: try rewrite <- H8 in H0; inversion H0.
  subst.
  assert (forall vers : version,
     In (tid1, read_item vers) t ->
     In (tid1, validate_read_item vers) t) as A1.
  {
    intros.
    simpl in *.
    assert ((tid2, commit_txn) = (tid1, read_item vers) \/ In (tid1, read_item vers) t). { right. auto. }
  apply H5 in H2. 
  destruct H2. inversion H2. auto.
  }
  assert (trace_tid_phase tid1 t = 3) as A2.
  { 
    simpl in H4.
    destruct (Nat.eq_dec tid1 tid2). contradiction.
    auto.
  }
  apply sto_trace_cons in H6.
  apply commit_txn_step with (tid := tid1) in H6; auto.

  assert (forall vers : version,
      In (tid2, read_item vers) ((tid1, commit_txn) :: t) -> 
      In (tid2, validate_read_item vers) ((tid1, commit_txn) :: t)) as A3.
  { 
    intros.
    simpl in H1. destruct H1. inversion H1.
    apply H11 in H1. 
    simpl. right. auto.
  }
  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: t) = 3) as A4.
  {
    simpl.
    destruct (Nat.eq_dec tid2 tid1).
    apply Nat.eq_sym in e. contradiction. auto.
  }
  apply commit_txn_step with (tid:= tid2) in H6; auto.
  
  rewrite <- H8 in *. 
  assert (forall vers : version,
     In (tid1, read_item vers) t ->
     In (tid1, validate_read_item vers) t) as A1.
  {
    intros.
    simpl in *.
    assert ((tid2, complete_write_item (S (trace_write_version t1))) = (tid1, read_item vers) \/ In (tid1, read_item vers) t). { right. auto. }
  apply H5 in H15. 
  destruct H15. inversion H15. auto.
  }
  assert (trace_tid_phase tid1 t = 3) as A2.
  { 
    simpl in H4.
    destruct (Nat.eq_dec tid1 tid2). contradiction.
    auto.
  }
  apply sto_trace_cons in H6.
  apply commit_txn_step with (tid := tid1) in H6; auto.
  
  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: t) = 4).
  {
    simpl. destruct (Nat.eq_dec tid2 tid1); auto. 
  }
  assert (locked_by (((tid1, commit_txn) :: t)) 0 = tid2).
  {
    simpl; auto.
  }
  assert (trace_tid_last_write tid2 ((tid1, commit_txn) :: t) = Some val).
  {
    simpl. destruct (Nat.eq_dec tid2 tid1); auto.
  }
  apply complete_write_item_step with (tid0:= tid2) (val:= val) in H6; auto.

  subst.
  assert (forall vers : version,
     In (tid1, read_item vers) t ->
     In (tid1, validate_read_item vers) t) as A1.
  {
    intros.
    simpl in *.
    assert ((tid2, commit_done_txn) = (tid1, read_item vers) \/ In (tid1, read_item vers) t). { right. auto. }
  apply H5 in H2. 
  destruct H2. inversion H2. auto.
  }
  assert (trace_tid_phase tid1 t = 3) as A2.
  { 
    simpl in H4.
    destruct (Nat.eq_dec tid1 tid2). contradiction.
    auto.
  }
  apply sto_trace_cons in H6.
  apply commit_txn_step with (tid := tid1) in H6; auto.
  
  assert (trace_tid_phase tid2 ((tid1, commit_txn) :: t) = 4).
  {
    simpl. destruct (Nat.eq_dec tid2 tid1); auto. 
  }
  assert (locked_by (((tid1, commit_txn) :: t)) 0 <> tid2).
  {
    simpl; auto.
  }
  apply commit_done_step with (tid0:= tid2)in H6; auto.

  apply sto_trace_cons in ST.
  inversion ST.
  all: try rewrite <- H10 in H0; inversion H0.

  rewrite <- H10 in *.
  assert (trace_tid_phase tid1 t = 4).
  {
    simpl in H4. destruct (Nat.eq_dec tid1 tid2). contradiction. auto. 
  }
  assert (locked_by t 0 = tid1).
  {
    simpl in H5; auto.
  }
  assert (trace_tid_last_write tid1 t = Some val).
  {
    simpl in H6. destruct (Nat.eq_dec tid1 tid2). contradiction. auto.
  }
  apply sto_trace_cons in H7.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.

  assert (forall vers : version,
     In (tid2, read_item vers) ((tid1, complete_write_item (S (trace_write_version t))) :: t) ->
     In (tid2, validate_read_item vers) ((tid1, complete_write_item (S (trace_write_version t))) :: t)) as A1.
  {
    intros.
    simpl in *. destruct H18. inversion H18.
    apply H13 in H18. auto.
  }
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version t))) :: t) = 3) as A2.
  { 
    simpl. destruct (Nat.eq_dec tid2 tid1). apply Nat.eq_sym in e. contradiction. auto.
  }
  apply commit_txn_step with (tid := tid2) in H7; auto.

  rewrite <- H10 in *.
  simpl in H5.
  assert (trace_tid_phase tid1 t = 4).
  {
    simpl in H4. destruct (Nat.eq_dec tid1 tid2). contradiction. auto. 
  }
  assert (trace_tid_phase tid1 t > 0).
  rewrite H16. omega.
  apply trace_phase_nonzero in H17.
  rewrite <- H5 in H17. omega. auto. 
  
  rewrite <- H10 in *.
  assert (trace_tid_phase tid1 t = 4).
  { 
    simpl in H4. destruct (Nat.eq_dec tid1 tid2). contradiction. auto.
  }
  assert (locked_by t 0 = tid1).
  {
    simpl in H5; auto.  
  }
  assert (trace_tid_last_write tid1 t = Some val).
  { 
    simpl in H6. destruct (Nat.eq_dec tid1 tid2); auto.
  }
  apply sto_trace_cons in H7.
  apply complete_write_item_step with (tid0:= tid1) (val:= val) in H7; auto.
  
  assert (trace_tid_phase tid2 ((tid1, complete_write_item (S (trace_write_version t))) :: t) = 4).
  {
    simpl. destruct (Nat.eq_dec tid2 tid1); auto.
  }
  assert (locked_by (((tid1, complete_write_item (S (trace_write_version t))) :: t)) 0 <> tid2).
  { 
    simpl. 
    assert (trace_tid_phase tid2 t > 0).
    rewrite H12. omega.
    apply trace_phase_nonzero in H19. omega. auto.
  }
  apply commit_done_step with (tid0:= tid2) in H7; auto.
  
  apply sto_trace_cons in ST.
  inversion ST.
  all: try rewrite <- H10 in H0; inversion H0.

  rewrite <- H10 in *.
  assert (trace_tid_phase tid1 t = 4).
  {
    simpl in H4. destruct (Nat.eq_dec tid1 tid2). contradiction. auto. 
  }
  assert (locked_by t 0 <> tid1).
  {
    simpl in H5; auto.
  }
  apply sto_trace_cons in H6.
  apply commit_done_step with (tid0:= tid1) in H6; auto.

  assert (forall vers : version,
     In (tid2, read_item vers) ((tid1, commit_done_txn) :: t) ->
     In (tid2, validate_read_item vers) ((tid1, commit_done_txn) :: t)) as A1.
  {
    intros.
    simpl in *. destruct H17. inversion H17.
    apply H13 in H17. auto.
  }
  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: t) = 3) as A2.
  { 
    simpl. destruct (Nat.eq_dec tid2 tid1). apply Nat.eq_sym in e. contradiction. auto.
  }
  apply commit_txn_step with (tid := tid2) in H6; auto.

  rewrite <- H10 in *.
  assert (trace_tid_phase tid1 t = 4).
  {
    simpl in H4. destruct (Nat.eq_dec tid1 tid2). contradiction. auto. 
  }
  assert (locked_by t 0 <> tid1).
  {
    rewrite H13. auto.
  }
  apply sto_trace_cons in H6.
  apply commit_done_step with (tid0:= tid1) in H6; auto.

  assert (trace_tid_phase tid2 ((tid1, commit_done_txn) :: t) = 4).
  { 
    simpl. destruct (Nat.eq_dec tid2 tid1); auto.
  }
  assert (locked_by ((tid1, commit_done_txn) :: t) 0 = tid2).
  {
    simpl; auto.
  }
  assert (trace_tid_last_write tid2 ((tid1, commit_done_txn) :: t) = Some val).
  {
    simpl. destruct (Nat.eq_dec tid2 tid1); auto.
  }
  apply complete_write_item_step with (tid0:= tid2) (val:= val) in H6; auto.

  rewrite <- H10 in *.
  assert (trace_tid_phase tid1 t = 4).
  {
    simpl in H4. destruct (Nat.eq_dec tid1 tid2). contradiction. auto. 
  }
  assert (locked_by t 0 <> tid1).
  {
    simpl in H5. auto.
  }
  apply sto_trace_cons in H6.
  apply commit_done_step with (tid0:= tid1) in H6; auto.

  assert (trace_tid_phase tid2 (((tid1, commit_done_txn) :: t)) = 4).
  { 
    simpl. destruct (Nat.eq_dec tid2 tid1); auto.  
  }
  assert (locked_by ((tid1, commit_done_txn) :: t) 0 <> tid2).
  {
    simpl. auto.
  }
  apply commit_done_step with (tid0:= tid2) in H6; auto.
Qed. 

Lemma naive_swap tid1 tid2 action1 action2 t:
  unconflicted_sto_trace ((tid1, action1) :: (tid2, action2) :: t)
  -> tid1 <> tid2
  -> swappable tid1 action1 tid2 action2
  -> unconflicted_sto_trace ((tid2, action2):: (tid1, action1) :: t).
Proof.
  intros UST NE SW.
  inversion UST.
  assert (In (tid1, action1) ((tid1, action1) :: (tid2, action2) :: t)).
  simpl; auto.
  apply H0 in H3.
  simpl in H3.
  destruct (Nat.eq_dec tid1 tid1).
  assert (In (tid2, action2) ((tid1, action1) :: (tid2, action2) :: t)).
  simpl; auto.
  apply H0 in H4.
  simpl in H4.
  destruct (Nat.eq_dec tid2 tid1).
  apply Nat.eq_sym in e0. contradiction.
  destruct (Nat.eq_dec tid2 tid2).
  apply sto_trace_can_swap in H; auto.
  assert (forall (tid0 : tid) (action0 : action),
     In (tid0, action0) ((tid2, action2) :: (tid1, action1) :: t) ->
     trace_tid_phase tid0 ((tid2, action2) :: (tid1, action1) :: t) = 4).
  intros.
  assert (In (tid0, action0) ((tid2, action2) :: (tid1, action1) :: t) -> In (tid0, action0) ((tid1, action1) :: (tid2, action2) :: t)).
  intros.
  simpl. simpl in H6. destruct H6. right. left. auto.
  destruct H6. left. auto.
  auto.
  apply H6 in H5. apply H0 in H5. simpl in H5. simpl.
  destruct (Nat.eq_dec tid0 tid1).
  destruct (Nat.eq_dec tid0 tid2).
  auto. auto.
  destruct (Nat.eq_dec tid0 tid2).
  auto. auto.
  assert (forall (tid0 : tid) (t1 t2 : list (tid * action)),
     (tid2, action2) :: (tid1, action1) :: t =
     t1 ++ (tid0, lock_write_item) :: t2 ->
     no_outstanding_read tid0 t2 (trace_outstanding_read_list tid0 t2)).
  intros.

Admitted.

Lemma basic_swap tid1 tid2 action1 action2 t1 t2:
  unconflicted_sto_trace (t1 ++ (tid1, action1) :: (tid2, action2) :: t2)
  -> swappable tid1 action1 tid2 action2
  -> unconflicted_sto_trace (t1 ++ (tid2, action2):: (tid1, action1) :: t2).
Proof.
  intros UST SW.
  induction SW.
Admitted.

Lemma trace_if_swappable_has_at_least_two_steps t1 t2 :
  swapstep1 t1 t2
  -> exists tid1 tid2 action1 action2 t t',
     t1 = t ++ (tid1, action1) :: (tid2, action2) :: t' /\
     t2 = t ++ (tid2, action2) :: (tid1, action1) :: t'.
Proof.
  intros.
  inversion H.
  all: exists tid1; exists tid2; exists action1; 
  exists action2; exists t0; exists t3; auto.
Qed.

Lemma swapstep1_preserve_ust t1 t2 :
  unconflicted_sto_trace t1
  -> swapstep1 t1 t2
  -> unconflicted_sto_trace t2.
Proof.
  intros.
  assert (swapstep1 t1 t2). { auto. }
  apply trace_if_swappable_has_at_least_two_steps in H0.
  destruct H0 as [t' [t [action2 [action1 [tid2 [ tid1 H0]]]]]].
  destruct H0.
  subst.
  apply basic_swap; auto.
  apply swapstep_swappable with (t1 := tid2) (t2 := tid1). auto.
Qed.

Lemma swapsteps_preserve_ust t1 t2 :
  unconflicted_sto_trace t1 
  -> swapsteps t1 t2
  -> unconflicted_sto_trace t2.
Proof.
  intros UST SS.
  induction SS.
  now rewrite <- H.
  apply IHSS in UST.
  now apply swapstep1_preserve_ust in H.
Qed.


Lemma is_serial tr :
  unconflicted_sto_trace tr ->
  check_is_serial_trace (create_serialized_trace2 tr (seq_list tr)).
Proof.
  intros.
  induction H; subst; simpl; auto.
  
  simpl.
  induction t.
  simpl. auto.
Admitted.

Lemma is_sto_trace tr :
  unconflicted_sto_trace tr ->
  unconflicted_sto_trace (create_serialized_trace2 tr (seq_list tr)).
Proof.
  intros UST.
  assert (swapsteps tr (create_serialized_trace2 tr (seq_list tr))).
  now apply create_serialized_trace_is_by_swapsteps in UST.
  now apply swapsteps_preserve_ust with (t1:=tr).
Qed.


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

Lemma is_sto_trace tr:
  sto_trace (filter_sto_trace tr) ->
  sto_trace (create_serialized_trace2 (filter_sto_trace tr) (seq_list (filter_sto_trace tr))).
Proof.
  intros.
  induction tr. simpl; auto.
  destruct a. destruct a.
  all: simpl; auto.
  simpl in H.
  clear IHtr.
  simpl. auto.
  destruct a. destruct a.
  all: simpl in *; auto.
  destruct (Nat.eq_dec t t1); subst.
  auto.
  inversion H.
  destruct (Nat.eq_dec t t1); subst.
  auto. 
  simpl in *.
  
  


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
Admitted.

  
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

Lemma is_sto_trace_start t s1 first:
  sto_trace t ->
  seq_list t = first :: s1 ->
  sto_trace (create_serialized_trace t [first]).
Proof.
Admitted.

Lemma sto_trace_single tid t:
  sto_trace ((tid, seq_point) :: t)
  -> sto_trace (create_serialized_trace t (seq_list t))
  -> sto_trace ((trace_tid_actions tid ((tid, seq_point) :: t))
      ++ (create_serialized_trace t (seq_list t))).
Proof.
  intros.
  assert ((trace_tid_actions tid ((tid, seq_point) :: t)) = 
    create_serialized_trace ((tid, seq_point) :: t) [tid]). {
    admit.
  }
  rewrite H1.
  assert (sto_trace (create_serialized_trace ((tid, seq_point) :: t) [tid])). {
    apply is_sto_trace_start with (t := ((tid, seq_point) :: t)) (s1 := (seq_list t)) (first := tid).
    auto. simpl. auto.
  }
  clear H1.
  functional induction (create_serialized_trace ((tid, seq_point) :: t) [tid]).
  - simpl; auto.
  - 



  induction (create_serialized_trace ((tid, seq_point) :: t) [tid]).
  - simpl; auto.
  - apply sto_trace_cons in H2. apply IHt0 in H2.





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

forall t swap once t  = t
forall t2 not swapstep1 t t2
