(** FORMALIZATION OF SYSTEM F USING LOCALLY NAMELESS APPROACH **)
Import Coq.Init.Nat.
Require Import List.
Require Import Lia.
Import ListNotations.
Require Import Coq.NArith.BinNat.
Require Import Coq.Init.Datatypes.

(* Define the basic unit of a variable *)
Definition atom_tm := nat.
Definition atom_ty := nat.

Axiom infinite_atoms_ty : exists L, forall x : atom_ty, In x L.
Axiom choose_fresh_ty : forall L : list atom_ty, exists x, ~ In x L.

Axiom infinite_atoms_tm : exists L, forall x : atom_tm, In x L.
Axiom choose_fresh_tm : forall L : list atom_tm, exists x, ~ In x L.

(* Define the types in the system *)
Inductive ty : Type :=
  | ty_bvar : nat -> ty               (* bound type variable, using de Bruijn index *)
  | ty_fvar : atom_ty -> ty           (* free type variable, using atoms *)
  | ty_arrow : ty -> ty -> ty         (* function type *)
  | ty_forall : ty -> ty -> ty.             (* universal type *)

(* Define the terms in the system *)
Inductive tm : Type :=
  | tm_bvar : nat -> tm              (* bound term variable, using de Bruijn index *)
  | tm_fvar : atom_tm -> tm          (* free term variable, using atoms *)
  | tm_abs : ty -> tm -> tm          (* lambda abstraction with type annotation *)
  | tm_app : tm -> tm -> tm          (* application *)
  | tm_ttabs : ty -> tm -> tm              (* type abstraction *)
  | tm_ttapp : tm -> ty -> tm.       (* type application *)

(* Contexts *)
(* Type context associates free term variables (atoms) with their types *)
Definition type_context := list (atom_tm * ty).

(* Kind context simply lists the free type variables *)
Definition kind_context := list atom_ty.

(** Implement 'term' check - there are no free de bruijn indices 
whether at the term level or the type level*)
Inductive type_ty : nat -> ty -> Prop :=
| type_bvar : forall k n,
    n < k -> type_ty k (ty_bvar n)
| type_fvar : forall k X,
    type_ty k (ty_fvar X)
| type_arrow : forall k T1 T2,
  type_ty k T1 ->
  type_ty k T2 ->
  type_ty k (ty_arrow T1 T2)
| type_forall : forall k T1 T2,
    type_ty (S k) T2 ->
    type_ty k (ty_forall T1 T2).
Definition closed_ty (T: ty) := type_ty 0 T.

Inductive term_tm : nat -> tm -> Prop :=
| term_bvar : forall k n,
    n < k ->
    term_tm k (tm_bvar n)
| term_fvar : forall k x,
    term_tm k (tm_fvar x)
| term_abs : forall k T t,
    type_ty k T ->
    term_tm (S k) t ->
    term_tm k (tm_abs T t)
| term_app : forall k t1 t2,
    term_tm k t1 ->
    term_tm k t2 ->
    term_tm k (tm_app t1 t2)
| term_ttabs : forall k T t,
    type_ty k T ->
    term_tm (S k) t ->
    term_tm k (tm_ttabs T t)
| term_ttapp : forall k t T,
    term_tm k t ->
    type_ty k T ->
    term_tm k (tm_ttapp t T).
Definition closed_tm (t: tm) := term_tm 0 t.

(* Open a type with a type *)
(* Opening T with X *)
Fixpoint open_ty_helper (T : ty) (X : ty) (N : nat) : ty :=
  match T with
  | ty_bvar M => if N =? M then X else T
  | ty_fvar Y => T
  | ty_arrow T1 T2 => ty_arrow (open_ty_helper T1 X N) (open_ty_helper T2 X N)
  | ty_forall T1 T2 => ty_forall (open_ty_helper T1 X N) (open_ty_helper T2 X (S N))
  end.
Definition open_ty_ty T X := open_ty_helper T (ty_fvar X) 0.

(* Open term with term *)
Fixpoint open_tm_tm_h (t : tm) (s : tm) (n : nat) : tm :=
    match t with
    | tm_bvar m => if n =? m then s else t
    | tm_fvar x => t
    | tm_abs T t' => tm_abs T (open_tm_tm_h t' s (S n))
    | tm_app t1 t2 => tm_app (open_tm_tm_h t1 s n) (open_tm_tm_h t2 s n)
    | tm_ttabs T t' => tm_ttabs T (open_tm_tm_h t' s n)
    | tm_ttapp t' T => tm_ttapp (open_tm_tm_h t' s n) T
    end.
Definition open_tm_tm t s := open_tm_tm_h t (tm_fvar s) 0.

(* Open term with type *)
Fixpoint open_tm_ty_h (t : tm) (X : ty) (n : nat) : tm :=
    match t with
    | tm_bvar m => t
    | tm_fvar x => tm_fvar x
    | tm_abs T t' => tm_abs (open_ty_helper T X n) (open_tm_ty_h t' X (S n))
    | tm_app t1 t2 => tm_app (open_tm_ty_h t1 X n) (open_tm_ty_h t2 X n)
    | tm_ttabs T t' => tm_ttabs (open_ty_helper T X n) (open_tm_ty_h t' X (S n))
    | tm_ttapp t' T => tm_ttapp (open_tm_ty_h t' X n) (open_ty_helper T X n)
    end.
Definition open_tm_ty t X := open_tm_ty_h t (ty_fvar X) 0.

(* Typing rules define when a term has a certain type *)
Inductive has_type : type_context -> kind_context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma Delta x T,
      List.In (x, T) Gamma ->
      has_type Gamma Delta (tm_fvar x) T

  | T_Abs : forall Gamma Delta T1 t2 T2 L,
      closed_ty T1 ->
      (forall x, ~ (List.In x L) -> 
      has_type ((x, T1) :: Gamma) Delta (open_tm_tm t2 x) T2) ->
      has_type Gamma Delta (tm_abs T1 t2) (ty_arrow T1 T2)

  | T_App : forall Gamma Delta t1 t2 T1 T2,
      has_type Gamma Delta t1 (ty_arrow T1 T2) ->
      has_type Gamma Delta t2 T1 ->
      has_type Gamma Delta (tm_app t1 t2) T2

  | T_TAbs : forall Gamma Delta t V T L,
      (forall X, ~ (List.In X L) -> 
      has_type Gamma (X :: Delta) (open_tm_ty t X) (open_ty_ty T X)) ->
      has_type Gamma Delta (tm_ttabs V t) (ty_forall V T)

  | T_TApp : forall Gamma Delta t T1 T2,
    has_type Gamma Delta t (ty_forall T1 T2) ->
    closed_ty T2 ->
    has_type Gamma Delta (tm_ttapp t T1) (open_ty_helper T2 T1 0).

(** Values *)

Inductive value : tm -> Prop :=
  | value_abs  : forall X t, closed_tm (tm_abs X t) ->
                 value (tm_abs X t)
  | value_tabs : forall X t, closed_tm (tm_ttabs X t) ->
                 value (tm_ttabs X t).

(** Small step reduction rules *)

Inductive step : tm -> tm -> Prop :=
  (* Context rules for term application *)
  | ST_App1 : forall t1 t1' t2,
    closed_tm t2 ->
    step t1 t1' ->
    step (tm_app t1 t2) (tm_app t1' t2)

  | ST_App2 : forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
    step (tm_app v1 t2) (tm_app v1 t2')

  (* Context rules for type application *)
  | ST_TApp : forall t1 t1' T,
    closed_ty T ->
    step t1 t1' ->
    step (tm_ttapp t1 T) (tm_ttapp t1' T)

  (* Term Beta-reduction *)
  | ST_Abs : forall T t1 v2,
    closed_tm (tm_abs T t1) ->
    value v2 ->
    step (tm_app (tm_abs T t1) v2) (open_tm_tm_h t1 v2 0)

  (* Type beta-reduction *)
  | ST_TAbs : forall T1 t T2,
    closed_tm (tm_ttabs T1 t) ->
    closed_ty T2 ->
    step (tm_ttapp (tm_ttabs T1 t) T2) (open_tm_ty_h t T2 0). 

(** Our goal is to prove preservation and progress *)

Definition preservation := forall G D e e' T,
  has_type G D e T ->
  step e e' ->
  has_type G D e' T.

Definition progress := forall e T,
  has_type [] [] e T ->
     value e
  \/ exists e', step e e'.

(** Lemmas *)

(** Canonical Forms *)

Lemma canonical_form_abs : forall t T1 T2,
  value t -> has_type [] [] t (ty_arrow T1 T2) ->
  exists V, exists t1, t = tm_abs V t1.
Proof.
  intros t T1 T2 Val HT. 
  induction HT; intros; inversion Val; subst; try contradiction.
  - exists T0. exists t2. reflexivity.
  - destruct (choose_fresh_ty L) as [X notInL].
    specialize (H X notInL). specialize (H0 X notInL).
    destruct Val.
Admitted.

Lemma canonical_form_tabs : forall t T1 T2,
  value t -> has_type [] [] t (ty_forall T1 T2) ->
  exists V, exists t1, t = tm_ttabs V t1.
Proof.
Admitted.

(* Substitution Lemma *)

Lemma nat_eqb_eq : forall n m : nat,
  n =? m = true <-> n = m.
Proof.
  induction n; destruct m; split; intros; try reflexivity; try discriminate.
  - simpl in H. apply IHn in H. rewrite H. reflexivity.
  - inversion H. simpl. destruct IHn with m; subst. apply H2. reflexivity.
Qed.

Lemma nat_eqb_neq : forall n m : nat,
  n =? m = false <-> n <> m.
Proof.
  induction n; destruct m; split; intros; try reflexivity; try discriminate.
  - destruct H. reflexivity.
  - apply IHn in H. congruence.
  - simpl. rewrite IHn. congruence. 
Qed.

Lemma in_cons_neq_tail : forall (A B : Type) (a x : A) (U T : B) (l : list (A * B)),
  In (a, U) ((x, T) :: l) -> a <> x -> In (a, U) l.
Proof.
  intros A B a x U T l H Hneq.
  destruct H as [H_head | H_tail].
  - inversion H_head; subst.
    contradiction Hneq; reflexivity.
  - exact H_tail.
Qed.

Lemma subst_bvar_reflexivity: forall t k,
  open_tm_tm_h (tm_bvar k) t k = t.
Proof.
  intros. simpl.
  destruct (k =? k) eqn: H_eq.
  - reflexivity.
  - apply nat_eqb_neq in H_eq. contradiction.
Qed.

Lemma subst_bvar_depth_irrelevant: forall t n k,
  n > k ->
  open_tm_tm_h (tm_bvar n) t k = tm_bvar n.
Proof.
  intros. simpl.
  destruct (k =? n) eqn: H_eq.
  - apply nat_eqb_eq in H_eq; subst. lia.
  - reflexivity.
Qed.

Lemma substitution_tm : forall Gamma Delta x t e T1 T2,
  has_type ((x, T1) :: Gamma) Delta t T2 ->
  has_type Gamma Delta e T1 ->
  has_type Gamma Delta (open_tm_tm_h t e 0) T2.
Proof.
  intros Gamma Delta x t e T U Ht He.
  generalize dependent T.
  induction t; intros T Ht; inversion Ht; simpl; subst; eauto.
  -
Admitted.

Lemma substitution_ty : forall Gamma Delta X T t U,
  has_type Gamma (X :: Delta) t T ->
  closed_ty U ->
  has_type Gamma Delta (open_tm_ty_h t U 0) T.
Proof.
Admitted.