From Coq Require Export String.
Require Setoid.
From Coq Require Export Lists.List.
Require Import FunInd Recdef. 
Require Import Psatz.
Require Import ZArith.
From Equations Require Import Equations.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil) .
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).


Inductive lheap : Type :=
  | L 
  | N (t1 : lheap) (v : nat) (r : nat) (t2 : lheap )
  .

Definition isEmpty (h : lheap) : bool :=
	match h with 
	| L => true
	| _ => false
	end.

Example testIsEmptyT : isEmpty L = true.
Proof.
reflexivity.
Qed.

Example testIsEmptyF : isEmpty (N L 1 1 L)= false.
Proof.
reflexivity.
Qed.

Definition rank (h : lheap) : nat :=
	match h with 
	| L => 0
	| N _ _ r _ => r 
	end.

Example testRankL : rank L = 0.
Proof.
reflexivity.
Qed.

Example testRank : rank (N L 1 1 L ) = 1.
Proof.
reflexivity.
Qed.

Definition makeN (x : nat) (a b : lheap) :=
	if rank b <=? rank a then N a x (S (rank b) ) b 
	else N b x (S (rank a) ) a.

Example testMakeN : 
	makeN 2 (N L 1 1 L) (N L 1 1 L) = N (N L 1 1 L) 2 2 (N L 1 1 L).
Proof.
reflexivity.
Qed.

Fixpoint size (h : lheap) : nat :=
	match h with 
	| L => 0
	| N a _ _ b => size a + size b + 1
	end.

Example testSize1 : 
	size L = 0.
Proof.
reflexivity.
Qed.

Example testSize2 : 
	size (N L 1 1 L) = 1.
Proof.
reflexivity.
Qed.

Example testSize3 : 
	size (N (N (N L 1 1 L) 1 1 L) 0 1 L) = 3.
Proof.
reflexivity.
Qed.

Definition f (p : lheap*lheap) := 
	size (fst p) + size (snd p).

Definition g (p p' : lheap*lheap) := 
	f p < f p'.

Lemma gwf :
	well_founded g.
Proof.
apply (well_founded_lt_compat (lheap* lheap) f).
intros.
now unfold g.
Qed.

#[ global ] Instance WF : WellFounded g := gwf.

Equations mergep (p : (lheap*lheap)) : lheap by wf p g := 
	mergep (L,h) := h;
	(* mergep ((N a1 x r1 b1),L) := N a1 x r1 b1; *)
	mergep (h,L) := h;
	mergep (N a1 x r1 b1, N a2 y r2 b2 ) := if x <=? y then makeN x a1 (mergep (b1, (N a2 y r2 b2))) 
																					else makeN y a2 (mergep ((N a1 x r1 b1), b2))
.
Next Obligation.
unfold g. cbn. lia.
Defined.

Next Obligation.
unfold g. cbn. lia.
Defined.

Definition merge (h1 h2 : lheap) : lheap := 
	mergep (h1, h2).

Theorem mergeEq1 : forall (h : lheap), merge L h = h.
Proof.
intro h.
unfold merge. apply mergep_equation_1.
Qed.

Theorem mergeEq2 : forall (h : lheap), merge h L = h.
Proof.
intro h.
unfold merge. destruct h.
	- apply mergep_equation_1.
	- apply mergep_equation_2.
Qed.

Theorem mergeEq3 : forall (a1 : lheap) (x r1 : nat) (b1 a2 : lheap) (y r2 : nat) (b2 : lheap),
	merge (N a1 x r1 b1) (N a2 y r2 b2) = 
				(if x <=? y
 				then makeN x a1 (merge b1 (N a2 y r2 b2))
 				else makeN y a2 (merge (N a1 x r1 b1) b2)).
Proof.
intros.
unfold merge.
apply mergep_equation_3.
Qed.

Example testMergeL : 
	merge L (N L 1 1 L) = (N L 1 1 L).
Proof.
rewrite mergeEq1.
reflexivity.
Qed.

Example testMerge1 : 
	merge (N L 1 1 L) (N L 1 1 L) = makeN 1 L (N L 1 1 L).
Proof.
rewrite mergeEq3. simpl. rewrite mergeEq1. reflexivity.
Qed.

Example testMerge2 : 
	merge (N L 1 1 L) (N L 1 1 L) = N (N L 1 1 L) 1 1 L.
Proof.
rewrite mergeEq3. simpl. unfold makeN. rewrite mergeEq1. simpl. reflexivity.
Qed.

Example testMerge3 : 
	merge (N L 0 1 L) (N(N L 1 1 L) 1 1 L) = N (N (N L 1 1 L) 1 1 L) 0 1 L.
Proof.
rewrite mergeEq3. simpl. unfold makeN. rewrite mergeEq1. simpl. reflexivity.
Qed.

Definition insert (x : nat) (h : lheap) : lheap := 
	merge (N L x 1 L) h.

Example testInsert : 
	insert 0 L = N L 0 1 L. 
Proof.
unfold insert. rewrite mergeEq2. reflexivity.
Qed.

Definition findMin (h : lheap) : option nat := 
	match h with 
	 | L => None 
	 | N _ x _ _ => Some x 
	end.

Example testFindMin1 :
	findMin(N L 1 1 L) = Some 1.
Proof.
reflexivity.
Qed.

Example testFindMin2 :
	findMin L = None.
Proof.
reflexivity.
Qed.

Definition deleteMin (h : lheap) : lheap := 
	match h with 
	| L => L
	| N a x r b => merge a b
	end.

Example testDeleteMin1 :
	deleteMin (N L 1 1 L) = L.
Proof.
unfold deleteMin. rewrite mergeEq2. reflexivity.
Qed.

Example testDeleteMin2 :
	deleteMin L = L.
Proof.
unfold deleteMin. reflexivity.
Qed.

Example testDeleteMin3 :
	deleteMin (N(N (N L 1 1 L) 1 1 L) 0 1 L) = N (N L 1 1 L) 1 1 L.
Proof.
unfold deleteMin. rewrite mergeEq2. reflexivity.
Qed.

Inductive isLeftist : lheap -> Prop := 
	| Hil_L 																							: isLeftist L 
	| Hil_N (a b : lheap) (x n : nat) 
			(H : isLeftist a  ) (H1 : isLeftist b ) (H2 : rank b <= rank a) (H3 : n = rank b): 
			 isLeftist (N a x (S n) b)
.

Example testHeapIsLeftist : 
	isLeftist (N L 1 1 L).
Proof.
apply Hil_N.
	- apply Hil_L.
	- apply Hil_L.
	- simpl. lia.
	- reflexivity.
Qed.

Example testHeapIsLeftist2 : 
	isLeftist (N (N (N L 10 1 L) 9 2 (N(N L 12 1 L) 10 1 L)) 0 2 (N(N L 8 1 L) 3 1 L)).
Proof.
repeat ( try constructor; try (simpl; lia); try reflexivity).
Qed.

Definition val (h : lheap) := 
	match h with 
	| L => None 
	| N _ x _ _ => Some x 
	end.

Definition valCmp (x y : option nat ):=
	match x, y with 
	| None, None => true
	| None, Some _ => false
	| Some _, None => true
	| Some x, Some y => x <=? y
	end.

Definition heapCmp (a b : lheap) :=
	valCmp (val a) (val b).

Inductive isHeap : lheap -> Prop := 
| IH_L 					: isHeap L
| IH_N x r a b 	: (isHeap a) -> (isHeap b) -> (valCmp (Some x) (val a)) = true 
									-> (valCmp (Some x) (val b)) = true -> isHeap (N a x r b).

Example testIsHeap1 : 
	isHeap (N L 1 1 L).
Proof.
repeat constructor.
Qed.

Example testIsHeap2 : 
	isHeap (N (N (N L 10 1 L) 9 2 (N(N L 12 1 L) 10 1 L)) 0 2 (N(N L 8 1 L) 3 1 L)).
Proof.
repeat ( try constructor; try  lia).
Qed.

	(* Same elements *)
 
Fixpoint nbOcc (x :nat ) (h : lheap) : nat :=
	match h with
	| L => 0
	| N a y r b => if x =? y then S (nbOcc x a + nbOcc x b) 
														else nbOcc x a + nbOcc x b
	end.
	
Definition valEq  (x y : option nat) :=
	match x, y with
	| None, None => true
	| None, _ => false
	| _, None => false
	| Some x, Some y => x =? y
	end.
