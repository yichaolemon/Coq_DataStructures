Require Import EqNat.
Require Import PeanoNat.
Require Import String.
Require Import BinNums.
Require Import List.
Require Import Compare_dec.
Require Import Omega.
Set Implicit Arguments.


Section TREE.

(*
Type for the keys of the tree.
Could potentially be polymorphic, with requirements of decidable equality and total ordering.
*)
Definition K: Type := nat.

Variable V: Type.

Inductive Tree : Type :=
  | null : Tree
  | node : K->V->Tree->Tree->Tree. 

Fixpoint tree_all_keys (t: Tree) (p: K->Prop) : Prop := 
  match t with 
  | null => True 
  | node k v lt rt  => p k /\ (tree_all_keys lt p) /\ (tree_all_keys rt p)
  end. 

Definition tree_min (t: Tree) (k: K): Prop :=
  tree_all_keys t (fun k' => k' > k).

Definition tree_max (t: Tree) (k: K): Prop :=
  tree_all_keys t (fun k' => k' < k).

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

Lemma all_after_insert: forall t a v p, tree_all_keys t p -> p a -> tree_all_keys (tree_insert t a v) p.
Proof.
induction t; simpl; intros. 
auto. remember (a =? k) as c. destruct c. constructor. apply H. apply H. 
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

Lemma insert_proof : forall (tr: Tree) (a: K) (v: V), is_bst tr -> is_bst (tree_insert tr a v).
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

Definition BST_search (tr: BST) (k: K) : option V :=
  match tr with 
  | tree t proof_t       => tree_search t k
  end.

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

Theorem BST_insert_retrieve : forall tr k v, BST_search (BST_insert tr k v) k = Some v. 
Proof. 
unfold BST_search, BST_insert. induction tr; simpl; intros. apply insert_retrieve. 
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

Theorem insert_other_skip: forall tr k1 v k2,
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



Theorem element_found: forall tr k v,
  tree_search tr k = Some v -> In (k, v) (elements tr).
Proof.
induction tr; simpl; intros.
discriminate.
destruct (Nat.eq_dec k0 k).
- (* found at root *)
subst.
rewrite <- beq_nat_refl in H.
injection H; intros; subst.
apply in_the_middle.
- (* found in subtree *)
apply nat_not_equal in n.
rewrite n in H.
apply in_app_iff.
destruct (k0 <? k).
+ (* left subtree *)
apply IHtr1 in H.
left. assumption.
+ (* right subtree *)
apply IHtr2 in H.
right. apply in_cons. assumption.
Qed.


Fixpoint elements (tr: BST) : list (K * V) :=
  match tr with
  | null => nil
  | node k v ltr rtr => (elements ltr) ++ ((k, v) :: elements rtr)
  end.

Lemma in_the_middle: forall T (v: T) l1 l2, 
 v (l1 ++ v :: l2).
Proof.
intros.
apply in_app_iff. right. apply in_eq.
Qed.


Theorem element_not_found: forall tr k,
  tree_search tr k = None -> ~ In k (map fst (elements tr)).
Proof.
induction tr; simpl; intros.
easy.

Abort.

End TREE.



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
Definition big_tree := tree_insert (tree_insert (tree_insert (tree_insert base_tree 5 "totonut") 3 "mahalo") 6 "aloha") 4 "hello".

Example big_tree_search_5: tree_search big_tree 5 = Some "totonut".
Proof.
unfold big_tree.
rewrite insert_other_skip.
rewrite insert_other_skip.
rewrite insert_other_skip.
rewrite insert_retrieve.
easy. easy. easy. easy.
Qed.

End examples.
