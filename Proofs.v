From Coq Require Export String.
Require Import FunInd Recdef. 
Require Import Psatz.
Require Import ZArith.
From Equations Require Import Equations.
From STAGE Require Import Definitions.
From STAGE Require Import UsefulLemmas.
  
(* Leftist *)
Theorem leftistMerge : forall (a b : lheap), 
	isLeftist a -> isLeftist b -> isLeftist (merge a b).
Proof.
	induction a; induction b.
	- intros. rewrite mergeLN. assumption.
	- intros. rewrite mergeLN. assumption.
	- intros. rewrite mergeNL. assumption.
	- intros. destruct (v <=? v0) eqn:E. 
		+ rewrite mergeNN_true. 2:assumption.
			apply makeNIsLeftist.
			* exact (isLeftistChildA H).
			* apply IHa2. 2:assumption.
				exact  (isLeftistChildB H).
		+ rewrite mergeNN_false. 2:assumption.
			apply makeNIsLeftist.
			* exact (isLeftistChildA H0).
			* apply IHb2. assumption. exact (isLeftistChildB H0).
Qed.

Theorem leftistInsert : forall (x : nat) (a : lheap), 
	isLeftist a	-> isLeftist (insert x a).
Proof.
	intros.
	unfold insert.
	apply leftistMerge.
		- constructor; try constructor.
		- assumption.
Qed.

Theorem leftistDeleteMin : forall (a : lheap), 
	isLeftist a -> isLeftist (deleteMin a).
Proof.
	intros.
	unfold deleteMin.
	destruct a eqn:E.
		- assumption.
		- apply leftistMerge.
			+ apply (isLeftistChildA H).
			+ apply (isLeftistChildB H).
Qed.

(* Heap *)

Theorem heapMerge : forall (a b : lheap), isHeap a -> isHeap b -> isHeap (merge a b).
Proof.
	induction a; induction b.
		- intros. rewrite mergeLL. assumption.
		- intros. rewrite mergeLN. assumption.
		- intros. rewrite mergeNL. assumption.
		- intros. destruct ( v <=? v0) eqn:E. 
			+ rewrite mergeNN_true. 2:assumption.
				apply makeNIsHeap.
				* exact (isHeapChildA H).
				* apply IHa2. 2:assumption. exact (isHeapChildB H).
				* simpl. destruct (val a1) eqn:E1. 2:reflexivity.	
					apply Nat.leb_le. apply (isHeapValueChildA H). assumption.
				* simpl. destruct (merge a2 (N b1 v0 r0 b2)) eqn:E1.
					** simpl. reflexivity.
					** simpl. apply Nat.leb_le. apply (f_equal val) in E1. simpl in E1. 
						destruct (valCmp (Some v0) (val a2)) eqn:E2.
						++ rewrite valMergeVAT in E1.
							*** injection E1. intro. rewrite H1 in E. rewrite Nat.leb_le in E. assumption.
							*** exact (isHeapChildB H).
							*** assumption.
							*** assumption.
						++ rewrite valMergeVAF in E1.
							*** apply (isHeapValueChildB H). assumption.
							*** exact (isHeapChildB H).
							*** assumption.
							*** assumption.
			+ rewrite mergeNN_false. 2:assumption.
				apply makeNIsHeap.
				* exact (isHeapChildA H0).
				* apply IHb2. assumption. exact (isHeapChildB H0).
				* simpl. destruct (val b1) eqn:E1. 2:reflexivity.
					apply Nat.leb_le. apply (isHeapValueChildA H0). assumption.
				* simpl. destruct (merge (N a1 v r a2) b2) eqn:E1.
					** simpl. reflexivity.
					** simpl. apply Nat.leb_le. apply (f_equal val) in E1. simpl in E1. 
						destruct (valCmp (Some v) (val b2)) eqn:E2.
						++ rewrite valMergeVBT in E1.
							*** injection E1. intro. rewrite H1 in E. rewrite Nat.leb_nle in E. lia.
							*** exact (isHeapChildB H0).
							*** assumption.
							*** assumption.  
						++ rewrite valMergeVBF in E1.
							*** apply (isHeapValueChildB H0). assumption.
							*** exact (isHeapChildB H0).
							*** assumption.
							*** assumption.
Qed.

Theorem HeapInsert : forall (x : nat) (a : lheap),
 isHeap a	-> isHeap (insert x a).
Proof.
	intros.
	unfold insert.
	apply heapMerge. constructor; try constructor.
	assumption.
Qed.

Theorem HeapDeleteMin : forall (a : lheap), isHeap a	-> isHeap (deleteMin a).
Proof.
	intros.
	unfold deleteMin. destruct a. assumption.
	apply heapMerge.
		+ apply (isHeapChildA H).
		+ apply (isHeapChildB H).
Qed.

(* SameElements *)

Theorem nbOccMerge: forall (x :nat) (a b :lheap),
 nbOcc x a + nbOcc x b = nbOcc x (merge a b) .
Proof.
induction a; induction b; simpl.
	- rewrite mergeLL. reflexivity.
	- destruct (x =? v) eqn:E.
		+ rewrite mergeLN. unfold nbOcc at 3. rewrite E. fold nbOcc. reflexivity.
		+ rewrite mergeLN. unfold nbOcc at 3. rewrite E. fold nbOcc. reflexivity.
	- rewrite mergeNL. destruct (x =? v) eqn:E.
		+ unfold nbOcc at 3. rewrite E. fold nbOcc. lia. 
		+ unfold nbOcc at 3. rewrite E. fold nbOcc. lia.
	- destruct (v <=? v0 ) eqn:E.
		+ rewrite mergeNN_true. 2:assumption.
			rewrite nbOccMakeN. destruct (x =? v) eqn:E1; rewrite <-IHa2; 
			destruct (x =? v0) eqn:E2;
			unfold nbOcc at 7; rewrite E2; fold nbOcc; lia.
		+ rewrite mergeNN_false. 2:assumption.
			rewrite nbOccMakeN. destruct (x =? v) eqn:E1; rewrite <-IHb2;
			destruct (x =? v0) eqn:E2;
		 	unfold nbOcc at 6; rewrite E1; fold nbOcc; lia.
Qed.

Theorem nbOccInsert_true : forall (x y : nat) (h :lheap),
	x =? y = true -> nbOcc x (insert y h) = S (nbOcc x h ) .
Proof.
intros.
unfold insert. rewrite <-nbOccMerge. simpl. rewrite H. lia.
Qed.

Theorem nbOccInsert_false : forall (x y : nat) (h :lheap),
	x =? y = false -> nbOcc x (insert y h) = nbOcc x h .
Proof.
intros.
unfold insert. rewrite <-nbOccMerge. simpl. rewrite H. lia.
Qed.

Theorem nbOccDeleteMin_true : forall (x y r: nat) (a b : lheap),
 	x =? y = true -> nbOcc x (N a y r b) =  S (nbOcc x (deleteMin (N a y r b))).
Proof.
intros.
unfold deleteMin. rewrite <-nbOccMerge. simpl. now rewrite H.
Qed.

Theorem nbOccDeleteMin_false : forall (x y r: nat) (a b : lheap),
 	x =? y = false -> nbOcc x (N a y r b) =  nbOcc x (deleteMin (N a y r b)).
Proof.
intros.
unfold deleteMin. rewrite <-nbOccMerge. simpl. now rewrite H.
Qed.

Theorem nbOccDeleteMin_eq : forall (x : nat) (h : lheap),
 val h = Some x -> nbOcc x h =  S (nbOcc x (deleteMin h)).
Proof.
intros.
unfold deleteMin. destruct h. discriminate H.
simpl in H. rewrite <-nbOccMerge. simpl. inversion H. now rewrite Nat.eqb_refl.
Qed.

Theorem nbOccDeleteMin_neq : forall (x : nat) (h : lheap),
val h <> Some x -> nbOcc x h =  nbOcc x (deleteMin h).
Proof.
intros.
unfold deleteMin. destruct h. reflexivity.
simpl in H. rewrite <-nbOccMerge. simpl. destruct (x =? v)eqn:E. 2:reflexivity.
rewrite Nat.eqb_eq in E. rewrite E in H. exfalso. apply H. reflexivity.
Qed.