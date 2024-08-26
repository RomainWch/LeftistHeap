From Coq Require Export String.
Require Import FunInd Recdef. 
Require Import Psatz.
Require Import ZArith.
From Equations Require Import Equations.
From LEFTISTHEAP Require Import Definitions.

Lemma isLeftistChildA : forall {a b: lheap} {x r :nat}, 
isLeftist (N a x r b) -> isLeftist a.
Proof.
intros a b x r H.
inversion H.
assumption.
Qed.

Lemma isLeftistChildB : forall {a b: lheap} {x r :nat}, 
isLeftist (N a x r b) -> isLeftist b.
Proof.
intros a b x r H.
inversion H.
assumption.
Qed.

Theorem makeNIsLeftist : forall (x : nat) (a b : lheap), isLeftist a -> isLeftist b -> isLeftist (makeN x a b).
Proof.
intros.
unfold makeN.
destruct (rank b <=? rank a) eqn:E.
	- constructor; try assumption; try reflexivity.
	apply Nat.leb_le. assumption.
	(* Search "_ <=? _ " "_ <= _". *)
	- constructor; try assumption; try reflexivity.
	rewrite Nat.leb_nle in E. lia.
Qed.

Lemma sizeChildA: forall (a b : lheap) (x r : nat), S (size a) = size (N a x r b) - size b .
Proof.
intros. 
destruct a; destruct b; try (simpl; lia).
Qed. 

Lemma sizeChildB: forall (a b : lheap) (x r : nat), S (size b) = size (N a x r b) - size a .
Proof.
intros. 
destruct a; destruct b; try (simpl; lia).
Qed. 

Lemma mergeLL : merge L L = L.
Proof.
now rewrite mergeEq2.
Qed.

Lemma mergeLN : forall (n : lheap), merge L n = n.
Proof.
intro.
rewrite mergeEq1. reflexivity.
Qed.

Lemma mergeNL : forall (n : lheap), merge n L = n.
Proof.
intro.
rewrite mergeEq2. reflexivity.
Qed.

Lemma mergeNN_true : forall (a a' b b' : lheap) (x x' n n' : nat),
  x <=? x' = true -> merge (N a x n b) (N a' x'  n' b') = makeN x a (merge b (N a' x' n' b')).
	Proof.
	intros.
	rewrite mergeEq3.
	rewrite H. reflexivity.
Qed.

Lemma mergeNN_false : forall (a a' b b' : lheap) (x x' n n' : nat),
x <=? x' = false -> merge (N a x n b) (N a' x'  n' b') = makeN x' a' (merge (N a x n b) b').
Proof.
intros.
rewrite mergeEq3.
rewrite H. reflexivity.
Qed.

Lemma mergeNNLt_true : forall (a a' b b' : lheap) (x x' n n' : nat),
	x <? x' = true -> merge (N a' x'  n' b') (N a x n b) = makeN x a (merge (N a' x' n' b') b).
Proof.
intros.
rewrite mergeEq3.
destruct (x' <=? x) eqn:E.
	- rewrite Nat.leb_le in E. rewrite Nat.ltb_lt in H. lia.
	- reflexivity.
Qed. 

Lemma mergeNNLt_false : forall (a a' b b' : lheap) (x x' n n' : nat),
	x <? x' = false -> merge (N a' x'  n' b') (N a x n b) = makeN x' a' (merge  b'(N a x n b)).
Proof.
intros.
rewrite mergeEq3.
destruct (x' <=? x) eqn:E.
	- reflexivity.
	- rewrite Nat.leb_nle in E. rewrite Nat.ltb_nlt in H. lia.
Qed. 

	(* Heaps *)

Theorem makeNIsHeap: forall (x : nat) (a b : lheap), 
isHeap a -> isHeap b -> valCmp (Some x) (val a) = true -> valCmp (Some x) (val b) = true -> isHeap (makeN x a b).
Proof.
intros. 
unfold makeN. destruct (rank b <=? rank a) eqn:E. constructor; try assumption.
constructor; try assumption.
Qed.

Lemma isHeapChildA : forall {a b: lheap} {x r :nat}, 
isHeap (N a x r b) -> isHeap a.
Proof.
intros a b x r H.
inversion H; try constructor; try assumption.
Qed.

Lemma isHeapChildB : forall {a b: lheap} {x r :nat}, 
isHeap (N a x r b) -> isHeap b.
Proof.
intros a b x r H.
inversion H; try constructor; try assumption.
Qed.

Lemma isHeapValueChildA : forall {a b : lheap} {x v r: nat}, 
	isHeap (N a v r b) -> val a = Some x -> v <= x.
Proof. 
intros.
inversion H. rewrite H0 in H7. simpl in H7. apply Nat.leb_le. assumption.
Qed.

Lemma isHeapValueChildB : forall {a b : lheap} {x v r: nat}, 
	isHeap (N a v r b) -> val b = Some x -> v <= x.
Proof. 
intros.
inversion H. rewrite H0 in H8. simpl in H7. apply Nat.leb_le. assumption.
Qed.

Lemma valMakeN : forall {a b : lheap} {v: nat}, 
	val (makeN v a b) = Some v.
Proof.
intros.
unfold makeN.
destruct (rank b <=? rank a) eqn:E.
	- reflexivity.
	- reflexivity.
Qed.

Lemma valMergeVAT : forall {a a1 b1 : lheap} {v r: nat},
	isHeap a -> isHeap (N a1 v r b1) 
	-> (valCmp (Some v) (val a)  = true -> val (merge a (N a1 v r b1)) =  Some v).
Proof.
intros.
destruct a.
	- rewrite mergeLN. reflexivity.
	- simpl in H1.
	case_eq (v =? v0); intros.
		+ rewrite Nat.eqb_eq in H2. subst. rewrite mergeNN_true. 2:assumption.
		apply valMakeN.
		+ rewrite mergeNNLt_true.
		apply valMakeN.
		rewrite Nat.leb_le in H1.
		rewrite Nat.eqb_neq in H2.
		rewrite Nat.ltb_lt.
		lia.
Qed.  

Lemma valMergeVAF : forall {a a1 b1 : lheap} {v r: nat},
	isHeap a -> isHeap (N a1 v r b1) 
	-> (valCmp (Some v) (val a)  = false -> val (merge a (N a1 v r b1)) = val a).
Proof.
intros.
destruct a.
	- discriminate H1.
	- simpl in H1.
		case_eq (v =? v0); intros.
		+ rewrite Nat.eqb_eq in H2. subst. rewrite mergeNN_false. 2:assumption.
		apply valMakeN.
		+ rewrite mergeNNLt_false.
			apply valMakeN.
			rewrite Nat.leb_nle in H1.
			rewrite Nat.eqb_neq in H2.
			rewrite Nat.ltb_nlt.
			lia.
Qed.  

Lemma valMergeVBT : forall {a1 b b1 : lheap} {v r: nat},
	isHeap b -> isHeap (N a1 v r b1) 
	-> (valCmp (Some v) (val b)  = true -> val (merge (N a1 v r b1) b) =  Some v).
Proof.
intros.
destruct b.
	- rewrite mergeNL. reflexivity.
	- simpl in H1.
		case_eq (v =? v0); intros.
		+ rewrite Nat.eqb_eq in H2. subst. rewrite mergeNN_true. 2:assumption.
			apply valMakeN.
		+ rewrite mergeNNLt_false.
			apply valMakeN.
			rewrite Nat.leb_le in H1.
			rewrite Nat.eqb_neq in H2.
			rewrite Nat.ltb_nlt.
			lia.
Qed.  

Lemma valMergeVBF : forall {a1 b b1 : lheap} {v r: nat},
	isHeap b -> isHeap (N a1 v r b1) 
	-> (valCmp (Some v) (val b)  = false -> val (merge (N a1 v r b1) b) = val b).
Proof.
intros.
destruct b.
	- discriminate H1.
	- simpl in H1.
		case_eq (v =? v0); intros.
		+ rewrite Nat.eqb_eq in H2. subst. rewrite mergeNN_false. 2:assumption.
			apply valMakeN.
		+ rewrite mergeNNLt_true.
			apply valMakeN.
			rewrite Nat.leb_nle in H1.
			rewrite Nat.eqb_neq in H2.
			rewrite Nat.ltb_lt.
			lia.
Qed. 

(* Same elements *)

Lemma nbOccMakeN : forall (x y: nat) (a b : lheap),
	nbOcc x (makeN y a b) = if x =? y then S (nbOcc x a + nbOcc x b) 
	else nbOcc x a + nbOcc x b.
Proof.
intros.
destruct (x =? y) eqn:E;
unfold makeN; destruct (rank b <=? rank a); unfold nbOcc at 1;
rewrite E; fold nbOcc; lia.
Qed.


