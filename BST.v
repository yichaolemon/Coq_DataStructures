(******************************************************************
  Definitions of general tree and BST, where BST is constructed as 
  a tree with the proof that it's BST. 
  Functions such as insert, search, and equivalences between tree
  and list of elements from in-order tree traversal. 
  Various lemmas, theorems that prove properties of the functions. 
  
  Author: :p 
  *****************************************************************) 

Require Import EqNat.
Require Import PeanoNat.
Require Import String.
Require Import BinNums.
Require Import List.
Require Import Compare_dec.
Require Import Omega.
Set Implicit Arguments.


Section TREE.

(** Type for the keys of the tree.
  Could potentially be polymorphic, with requirements of decidable equality and total ordering. *)
Definition K: Type := nat.

Variable V: Type.

Inductive Tree : Type :=
  | null : Tree
  | node : K->V->Tree->Tree->Tree. 

(* general predicate *) 
Fixpoint tree_all_keys (t: Tree) (p: K->V->Prop) : Prop := 
  match t with 
  | null => True 
  | node k v lt rt  => p k v /\ (tree_all_keys lt p) /\ (tree_all_keys rt p)
  end. 


Definition tree_min (t: Tree) (k: K): Prop :=
  tree_all_keys t (fun k' _  => k' > k).

Definition tree_max (t: Tree) (k: K): Prop :=
  tree_all_keys t (fun k' _ => k' < k).

Fixpoint is_bst (t: Tree) : Prop := 
  match t with 
  | null            => True 
  | node k v lt rt  => (tree_max lt k) /\ (tree_min rt k) /\ (is_bst lt) /\ (is_bst rt)
  end. 

(* binary search tree *) 
Inductive BST : Type := 
  | tree : forall t, is_bst t -> BST.

Lemma null_bst_proof : is_bst null.
Proof.
repeat constructor. Qed. 

Definition null_BST : BST := 
  tree (null) null_bst_proof.

Check null_BST. 

Fixpoint tree_insert (tr: Tree) (a: K) (v: V) : Tree :=
  match tr with
  | null                => node a v null null
  | node key val ltr rtr    => if a =? key then node key v ltr rtr 
                           else (if a <? key then node key val (tree_insert ltr a v) rtr
                                 else node key val ltr (tree_insert rtr a v))
  end.

Lemma all_after_insert: forall t a v p, tree_all_keys t p -> p a v -> tree_all_keys (tree_insert t a v) p.
Proof.
induction t; simpl; intros. 
auto. remember (a =? k) as c. destruct c. constructor. symmetry in Heqc. apply Nat.eqb_eq in Heqc.
rewrite <- Heqc. apply H0. apply H. 
remember (a <? k) as d. destruct d; simpl. split; try (apply H). split. 
apply IHt1. apply H. apply H0. apply H. 
split; try (apply H). split. apply H. apply IHt2. apply H. apply H0.
Qed.

Lemma gt_lemma: forall a k, false = (a =? k) -> false = (a <? k) -> a > k.
Proof. intros.
assert (a <> k). { intro. apply Nat.eqb_eq in H1. rewrite H1 in H. discriminate. }
apply not_eq in H1. destruct H1.
apply Nat.ltb_lt in H1. rewrite H1 in H0. discriminate.
auto.
Qed.

(** Theorem: tree_insert works, invariance. 
    Crucial for the self-verifying definition of BST_insert *)
Theorem insert_proof : forall (tr: Tree) (a: K) (v: V), is_bst tr -> is_bst (tree_insert tr a v).
Proof.
intros tr a v. induction tr; simpl. easy. 
intros. remember (a =? k) as d. destruct d; simpl. 
  apply H. remember (a <? k) as c. destruct c.  simpl. 
  split; try (apply H). destruct H. 
  apply all_after_insert. apply H. symmetry in Heqc. apply Nat.ltb_lt in Heqc. apply Heqc.
  split; try (apply H). split. apply IHtr1. apply H. apply H. 
  simpl. split; try (apply H). split. 
  apply all_after_insert. apply H.
  apply gt_lemma; auto.
  split. apply H. apply IHtr2. apply H.
Qed.

Definition BST_insert (tr: BST) (a: K) (v: V) : BST := 
  match tr with
  | tree t proof_t  => tree (tree_insert t a v) (insert_proof t a v proof_t)
  end. 

Fixpoint tree_search (tr: Tree) (k: K) : option V :=
  match tr with
  | null => None
  | node key val ltr rtr => if k =? key then Some val
                            else (if k <? key then tree_search ltr k
                                  else tree_search rtr k)
  end.

Definition bst_search (tr: BST) (k: K) : option V :=
  match tr with 
  | tree t proof_t       => tree_search t k
  end.

(** Theorems for tree and BST: what is inserted is seachable. *) 
Theorem insert_retrieve: forall tr k v, tree_search (tree_insert tr k v) k = Some v.
Proof.
induction tr; simpl; intros.
- (* empty initial tree *)
rewrite <- beq_nat_refl. easy.
- (* nonempty initial tree *)
remember (k0 =? k) as match_root. destruct match_root; simpl.
+ (* inserting at root *)
rewrite <- Heqmatch_root. easy.
+ (* inserting at left or right. inductive case *)
remember (k0 <? k) as lt_root.
destruct lt_root; simpl; rewrite <- Heqmatch_root; rewrite <- Heqlt_root.
apply IHtr1. apply IHtr2.
Qed.

Theorem BST_insert_retrieve : forall tr k v, bst_search (BST_insert tr k v) k = Some v. 
Proof. 
unfold bst_search, BST_insert. induction tr; simpl; intros. apply insert_retrieve. 
Qed.


Lemma nat_not_equal: forall n m, n <> m <-> (n =? m) = false.
Proof.
intros.
destruct (Nat.eq_dec n m).
-
split. contradiction. intro not_same. apply Nat.eqb_eq in e. rewrite e in not_same. discriminate.
-
split; intro; try easy.
remember (n =? m) as same. symmetry in Heqsame. destruct same; try easy.
apply Nat.eqb_eq in Heqsame. contradiction.
Qed.

(** Theorems for tree and BST: search for a key after insersion for a different key 
    is unaffected by the insersion. *) 
Theorem tree_insert_skip: forall tr k1 v k2,
  k2 <> k1 -> tree_search (tree_insert tr k1 v) k2 = tree_search tr k2.
Proof.
intros. apply nat_not_equal in H. 
induction tr; simpl. 
- rewrite H. destruct ( k2 <? k1); reflexivity. 
- remember (k1 =? k) as c_isequal. destruct c_isequal; subst.
  + remember (k2 =? k) as d_isequal. destruct d_isequal; subst. 
  symmetry in Heqc_isequal. apply Nat.eqb_eq in Heqc_isequal.
  symmetry in Heqd_isequal. apply Nat.eqb_eq in Heqd_isequal.
  rewrite <- Heqd_isequal in Heqc_isequal. rewrite Heqc_isequal in H. 
  apply nat_not_equal in H. omega. 
  remember (k2 <? k) as c. destruct c; simpl. 
  rewrite <-  Heqd_isequal.  rewrite <- Heqc. reflexivity.
  rewrite <- Heqc.  rewrite <- Heqd_isequal. reflexivity. 
  + remember (k1 <? k) as d. destruct d; simpl. 
  rewrite IHtr1. reflexivity. rewrite IHtr2. reflexivity.
Qed.

Theorem bst_insert_skip : forall (tr:BST) k1 v k2,
  k2 <> k1 -> bst_search (BST_insert tr k1 v) k2 = bst_search tr k2.
Proof.
intros. destruct tr. eapply tree_insert_skip in H.
simpl. apply H. Qed.

(* get all elements in the tree, in order *) 
Fixpoint tree_elements (tr: Tree) : list (K * V) := 
  match tr with 
  | null            => nil
  | node k v lt rt  => (tree_elements lt) ++ (cons (k, v) (tree_elements rt))
  end.

Definition bst_elements (tr: BST) : list (K * V) :=
  match tr with 
  | tree t proof_t  => tree_elements t
  end. 

Definition sorted_helper (a: K*V) (ls: list (K*V)) : Prop := 
  match ls with 
  | nil             => True 
  | cons a' ls'     => if (fst a <? fst a') then True else False
  end. 

Fixpoint list_sorted (ls: list (K*V)) : Prop := 
  match ls with 
  | nil           => True 
  | cons a ls'    => (sorted_helper a ls') /\ list_sorted ls'
  end. 

(* a bunch of useful lemmas for proving the monotonicity *) 
Lemma tree_all_keys_elements: forall t k v p,
  In (k, v) (tree_elements t) -> tree_all_keys t p -> p k v.
Proof.
induction t; simpl; intros. inversion H.
apply in_app_iff in H. destruct H.
apply IHt1. apply H. apply H0.
simpl in H. destruct H. injection H; intros; subst. apply H0.
apply IHt2. apply H. apply H0.
Qed.


Lemma cons_sorted : forall rt p v, 
  list_sorted (tree_elements rt)
  -> tree_min rt p -> list_sorted ((p, v) :: (tree_elements rt)).
Proof. 
induction rt; simpl; try auto; intros. 
split. 
- inversion H0. remember (tree_elements rt1 ++ (k, v) :: tree_elements rt2) as ls. 
  destruct ls. simpl. auto. simpl.
  replace (p <? fst p0) with true. constructor. symmetry. apply Nat.ltb_lt. destruct p0. simpl.
  remember (tree_elements rt1) as rt_elts. destruct rt_elts; simpl in Heqls; injection Heqls; intros; subst.
+ omega.
+ destruct H2.
assert (In (k0, v1) (tree_elements rt1)). { rewrite <- Heqrt_elts. simpl. left. reflexivity. }
eapply tree_all_keys_elements in H4; try eauto. simpl in H4. omega.
- apply H. 
Qed. 

Lemma cons_ls_sorted : forall a l, 
  list_sorted (a :: l) -> list_sorted l. 
Proof. 
intros. simpl in H. destruct H. apply H0. Qed. 

Lemma app_sorted: forall l rt p v,
  list_sorted l -> list_sorted (tree_elements rt) ->
  tree_min rt p -> Forall (fun e => fst e < p) l ->
  list_sorted (l ++ (p, v) :: (tree_elements rt)).
Proof.
Opaque list_sorted.
induction l; simpl; intros.
- apply cons_sorted. assumption. assumption.
- Transparent list_sorted. simpl.
split.
+ simpl in H.
destruct l. simpl. replace (fst a <? p) with true. easy. inversion H2; subst.
symmetry. apply Nat.ltb_lt. assumption.
simpl. destruct p0. destruct a. simpl.
simpl in H. apply H.
+ apply IHl. eapply cons_ls_sorted; eauto. assumption. assumption. inversion H2; subst. assumption.
Qed.

Lemma max_lt_list : forall t p x, 
  tree_max t p -> In x (tree_elements t) -> fst x < p. 
Proof.
intros. 
destruct x. simpl. eapply tree_all_keys_elements in H. eauto . eauto.
Qed. 

Lemma concat_sorted : forall lt rt p v, 
  list_sorted (tree_elements lt) -> list_sorted (tree_elements rt)
  -> tree_max lt p -> tree_min rt p -> list_sorted ((tree_elements lt) ++ (p, v) :: (tree_elements rt)).
Proof. 
intros. 
apply app_sorted.
apply H.  apply H0. apply H2. 
apply Forall_forall. 
intros. eapply max_lt_list. eapply H1. apply H3.
Qed. 


(** Theorems for tree and BST: monotonicity of the elements. *) 
Lemma elements_tree_monotone : forall tr, 
  is_bst tr -> list_sorted (tree_elements tr). 
Proof. 
intros tr. induction tr; simpl. auto. 
intros. apply concat_sorted. apply IHtr1. apply H.
apply IHtr2. apply H. apply H.  apply H. 
Qed. 


Theorem elements_monotone : forall (tr: BST), 
  list_sorted (bst_elements tr). 
Proof. 
intros. destruct tr. simpl. apply elements_tree_monotone. apply i.
Qed.

(* useful lemmas for proving the main theorems below *) 
Lemma tree_found : forall tr k v, 
  tree_search tr k = Some v -> In (k, v) (tree_elements tr). 
Proof.
intros tr k v. 
induction tr; simpl. 
intro H. inversion H. 
remember (k =? k0) as a eqn:Heq. destruct a. 
- intro. symmetry in Heq. apply Nat.eqb_eq in Heq; subst. inversion H.
  rewrite <- H1. simpl. apply in_app_iff. right. simpl. left. reflexivity.
- remember (k <? k0) as a eqn:Hle. destruct a. 
  + intro. apply IHtr1 in H. eapply in_app_iff. left. apply H. 
  + intro. apply IHtr2 in H. eapply in_app_iff. right. apply in_cons. apply H.
Qed. 

Lemma tree_equiv_helper : forall k v k0 v0 tr1 tr2,
  In (k, v) (tree_elements (node k0 v0 tr1 tr2)) <-> 
  (k, v) = (k0, v0) \/ In (k, v) (tree_elements tr1) \/ In (k, v) (tree_elements tr2).
Proof. 
intros k v k0 v0 tr1 tr2. simpl. split. 
- intros. apply in_app_iff in H. inversion H. 
  right. left.  apply H0.
  simpl in H0. inversion H0. rewrite H1. auto. right. right. apply H1. 
- intros. apply in_app_iff. inversion H. simpl. rewrite H0. auto. 
  inversion H0. left. apply H1. simpl. right. right. apply H1. 
Qed.


Lemma tree_equiv_helper' : forall k v k0 v0 tr1 tr2, 
  tree_search (node k0 v0 tr1 tr2) k = Some v -> 
  (k0, v0) = (k, v) \/ tree_search tr1 k = Some v \/ tree_search tr2 k = Some v. 
Proof. 
simpl.
intros. 
remember (k =? k0) as a; destruct a. left. symmetry in Heqa.
apply Nat.eqb_eq in Heqa. subst. 
inversion H. auto. symmetry in Heqa.
remember (k <? k0) as b. destruct b. 
right. left. assumption. 
right. right. assumption.
Qed. 

(** Theorems for BST: the list of elements is equivalent to the tree nodes searchable  
  aka. all elements got by tree traversal can be found by tree search, vice versa *)  
Theorem tree_equiv : forall tr k v, 
  is_bst tr -> (In (k, v) (tree_elements tr) <-> tree_search tr k = Some v).
Proof. 
intros tr k v.
induction tr.
- (* null tree *) 
intros. split; intros; inversion H0.
- (* real stuff!! *) 
intros. split; try (apply tree_found). 
intros. simpl in H. 
apply tree_equiv_helper in H0.
destruct H. destruct H1. destruct H2. assert (H2' := H2). assert (H3' := H3).
apply IHtr1 in H2. apply IHtr2 in H3.
destruct H0. simpl. injection H0; intros; subst. replace (k0 =? k0) with true.
reflexivity. symmetry. apply Nat.eqb_eq. reflexivity. 
destruct H0. assert (H0' := H0). simpl.  eapply tree_all_keys_elements in H0; try eauto.
simpl in H0. 
replace (k =? k0) with false. apply Nat.ltb_lt in H0. rewrite H0. 
apply H2. apply H0'. symmetry. apply nat_not_equal. intro. omega. 
assert (H0' := H0). simpl. eapply tree_all_keys_elements in H0; try eauto. 
simpl in H0.
replace (k =? k0) with false. replace (k <? k0) with false. apply H3. apply H0'.
symmetry. remember (k <? k0) as Hfal. destruct Hfal. symmetry in HeqHfal. apply Nat.ltb_lt in HeqHfal.
omega. reflexivity. symmetry. apply nat_not_equal. omega. 
Qed.

Theorem bst_equiv : forall (tr:BST) k v,
  In (k, v) (bst_elements tr) <-> bst_search tr k = Some v. 
Proof.
intros. destruct tr. apply tree_equiv. apply i. Qed. 


(** Theorems for BST: if we can't find in search, we can't find in list, vice versa *) 
Theorem element_not_found: forall (tr:BST) k,
  bst_search tr k = None <-> ~ In k (map fst (bst_elements tr)).
Proof.
intros. split. 
- (* -> *) 
intros. intro. apply in_map_iff in H0. destruct H0. destruct H0. 
destruct x . apply bst_equiv in H1. simpl in H0. subst. 
rewrite H1 in H. discriminate. 
- (* <- *) 
intro. unfold not in H. 
assert (forall o, (forall v:V, ~ o = Some v) -> o = None). 
{ intros Hv. destruct Hv. intros. assert (Some v <> Some v).
apply H0. assert (Some v = Some v). reflexivity. contradiction. 
intros. reflexivity. }
apply H0 with (o:=bst_search tr k). intros. intro. 
apply bst_equiv in H1. apply H. apply in_map_iff. exists (k, v).
simpl. split; try auto.
Qed. 

Section REMOVE.

Fixpoint tree_find_remove_max (t: Tree) : (Tree * option (K * V)) :=
  match t with
  | null => (null, None)
  | node k v ltr null => (ltr, Some (k, v))
  | node k v ltr rtr => let (rtr_removed, max) := tree_find_remove_max rtr in
      (node k v ltr rtr_removed, max)
  end.

Definition tree_remove_root (t: Tree) : Tree :=
  match t with
  | null => null
  | node k v null rtr => rtr
  | node k v ltr null => ltr
  | node k v ltr rtr => let (ltr_removed, new_root) := tree_find_remove_max ltr in
    match new_root with None => t (* impossible *)
    | Some (k', v') => node k' v' ltr_removed rtr
    end
  end.

Fixpoint tree_remove (t: Tree) (k: K) : Tree :=
  match t with
  | null => null
  | node k' v ltr rtr => if k =? k' then tree_remove_root t
                         else if k <? k' then tree_remove ltr k else tree_remove rtr k
  end.

(** Theorems and lemmas which include remove *) 
Lemma remove_max_satisfies_all: forall t rm_t max p
  (REM: (rm_t, max) = tree_find_remove_max t)
  (SAT: tree_all_keys t p),
  tree_all_keys rm_t p.
Proof.
induction t; simpl; intros.
injection REM; intros; subst.
simpl. constructor.
destruct t2.
injection REM; intros; subst. apply SAT.
remember (tree_find_remove_max (node k0 v0 t2_1 t2_2)) as rm_max. destruct rm_max.
injection REM; intros; subst.
simpl.
split. apply SAT.
split. apply SAT.
apply IHt2 with o. auto. apply SAT.
Qed.

Lemma tree_find_remove_max_bst : forall t rm_t max
  (ISBST: is_bst t) (REMOVE: tree_find_remove_max t = (rm_t, max)), is_bst rm_t.
Proof.
induction t; simpl; intros.
+
injection REMOVE; intros; subst. simpl. constructor.
+ (* only induct down the right *) clear IHt1.
destruct ISBST as (MAX & MIN & LEFTBST & RIGHTBST).
destruct t2.
- (* rtr is null *)
injection REMOVE; intros; subst. assumption.
- (* rtr is not null *)
remember (tree_find_remove_max (node k0 v0 t2_1 t2_2)) as removed.
destruct removed.
injection REMOVE; intros; subst.
simpl.
split. assumption.
split. eapply remove_max_satisfies_all; eauto.
split. assumption.
eapply IHt2; eauto.
Qed.

Lemma tree_all_keys_trans: forall t (p q: K->V->Prop),
  (forall k v, p k v -> q k v) ->
  tree_all_keys t p ->
  tree_all_keys t q.
Proof.
induction t; simpl; intros.
constructor.
split. apply H. apply H0.
split. eapply IHt1; eauto. apply H0. eapply IHt2; eauto. apply H0.
Qed.

Lemma tree_max_in: forall t rm_t k v
  (REMOVE: tree_find_remove_max t = (rm_t, Some (k, v))), In (k, v) (tree_elements t).
Proof.
induction t; simpl; intros.
discriminate.
destruct t2.
injection REMOVE; intros; subst.
apply in_app_iff. right. simpl. auto.
remember (tree_find_remove_max (node k1 v1 t2_1 t2_2)) as removed. destruct removed.
injection REMOVE; intros; subst.
apply in_app_iff. right. apply in_cons. eapply IHt2; eauto.
Qed.

Lemma tree_find_remove_max_max: forall t rm_t k v
  (ISBST: is_bst t) (REMOVE: tree_find_remove_max t = (rm_t, Some (k, v))), tree_max rm_t k.
Proof.
induction t; simpl; intros.
injection REMOVE; intros; subst. unfold tree_max. simpl. constructor.
destruct t2.
- (* rtr is null *)
injection REMOVE; intros; subst.
apply ISBST.
- (* rtr is not null *)
remember (tree_find_remove_max (node k1 v1 t2_1 t2_2)) as removed.
destruct removed.
destruct ISBST as (MAX & MIN & LEFTBST & RIGHTBST).
injection REMOVE; intros; subst.
assert (tree_max t k0) as MAXRM. { eapply IHt2; eauto. }
assert (k < k0) as ROOTMAX. {
symmetry in Heqremoved. apply tree_max_in in Heqremoved.
eapply tree_all_keys_elements in Heqremoved; try eapply MIN.
simpl in Heqremoved. omega.
}
split.
apply ROOTMAX.
split; try apply MAXRM.
apply tree_all_keys_trans with (p := fun (k': K) (_: V) => k' < k).
intros. omega.
apply MAX.
Qed.

Lemma tree_find_remove_max_nonempty :
  forall t, t <> null -> exists m rm_t, tree_find_remove_max t = (rm_t, Some m).
Proof.
induction t; intros. 
- simpl. contradiction. 
- remember t2 as t2'.
  destruct t2'.
  + simpl. eauto. 
  + rewrite  Heqt2' in *. 
    assert (t2 <> null). { subst t2. intro. discriminate. } 
    apply IHt2 in H0. destruct H0. destruct H0. exists x. 
    simpl. destruct t2; try discriminate. rewrite H0. exists (node k v t1 x0). reflexivity.  
Qed.

Lemma tree_remove_root_bst: forall t rm_t (ISBST: is_bst t) (REMOVE: tree_remove_root t = rm_t),
  is_bst rm_t.
Proof.
Opaque tree_find_remove_max.
destruct t; simpl; intros.
subst. apply null_bst_proof.
destruct t1. subst. apply ISBST. 
destruct t2. subst. apply ISBST. 
remember (tree_find_remove_max (node k0 v0 t1_1 t1_2)) as tree_removed. 
destruct tree_removed.
 (* destructing on the tree_find_remove_max cases *) 
destruct o; simpl. 
- (* when o is some p *) 
destruct p. subst. simpl. symmetry in Heqtree_removed.
split.  eapply tree_find_remove_max_max; try (eapply Heqtree_removed). apply ISBST. 
split. assert (In (k2, v2) (tree_elements (node k0 v0 t1_1 t1_2))).
{ eapply tree_max_in; try (eapply Heqtree_removed). } 
apply tree_all_keys_trans with (p := fun (k': K) (_: V) => k' > k). 
intros. assert (k > k2). { eapply tree_all_keys_elements in H; try (eapply ISBST).
simpl in H. omega. } omega.
simpl. split; try (apply ISBST). 
split. eapply tree_find_remove_max_bst; try (eapply Heqtree_removed). apply ISBST. 
apply ISBST. 
- (* when o is None *) 
Transparent tree_find_remove_max. 
assert ((node k0 v0 t1_1 t1_2) <> null). {intro. discriminate. }
apply tree_find_remove_max_nonempty in H. destruct H. destruct H.
rewrite <- Heqtree_removed in H. discriminate. 
Qed. 


End REMOVE.

End TREE.


(** Some silly examples :p nothing super fancy here *) 
Section examples.

Definition null_nat := null nat.

Lemma sample_is_bst: is_bst (node 5 0 (node 4 0 null_nat null_nat) (node 6 0 null_nat null_nat)).
Proof. simpl. repeat constructor. Qed. 

Definition first_bst : BST nat :=
tree (node 5 0 (node 4 0 null_nat null_nat) (node 6 0 null_nat null_nat)) sample_is_bst.

Example insert_check1 : is_bst (node 5 0 (node 4 0 null_nat null_nat) (node 6 0 null_nat null_nat)). 
Proof.
remember (BST_insert (BST_insert (BST_insert (null_BST nat) 5 0) 4 0) 6 0) as a_bst.
destruct a_bst. simpl in Heqa_bst. injection Heqa_bst; intros. unfold null_nat. rewrite <- H.
apply i. Qed.

Example simple_example: tree_search (tree_insert (null nat) 5 3) 5 = Some 3.
reflexivity. Qed.

Local Open Scope string_scope.
Variable base_tree: BST string.
Definition big_tree := BST_insert (BST_insert (BST_insert (BST_insert (null_BST string) 5 "totonut") 3 "mahalo") 6 "aloha") 4 "hello".

Example big_tree_search_5: bst_search big_tree 5 = Some "totonut".
Proof.
unfold big_tree.
rewrite bst_insert_skip.
rewrite bst_insert_skip.
rewrite bst_insert_skip.
simpl.
easy. easy. easy. easy.
Qed.

End examples.
