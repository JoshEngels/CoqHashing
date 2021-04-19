(* Inductive variable: Type :=
  | Var: nat -> variable. *)

(* TODO: Change hashmap to take in any object using polymorphism *)
(* TODO: Switch to list of pairs? Might make things easier but also
seperating function and data more interesting *)
Require Import Coq.Lists.ListSet.
Require Import List.
Require Import Coq.Arith.Arith.
Require Coq.Arith.PeanoNat.
From Coq Require Import Lia.


Definition function := nat -> nat.

(* TODO: Change to coq injective definition *)
Definition injective (f : function) := forall a b, f a = f b -> a = b.

Lemma s_is_injective:
  injective S.
Proof.
  - unfold injective. intros. apply eq_add_S in H. apply H.
Qed.

(* Define hash map, basically a pair of a function and a set, where
the function is the hash function and the set is all of the  *)
Inductive hash_map : Type :=
  | hash (f: function) (elements: list nat).
Definition hash_input (h: hash_map) : list nat :=
  match h with
    | hash f l => l
  end.
Definition hash_function (h: hash_map) : function :=
  match h with
  | hash f l => f
end.

(* Remove an arbitrary element from the hash map *)
Definition remove_first_from_hash_map (map: hash_map) : hash_map :=
  match (hash_input map) with
  | nil => map 
  | h :: t => hash (hash_function map) t
  end.


Fixpoint function_range (f: function) (l : list nat): set nat :=
  match l with
  | nil => nil
  | h :: t => set_add Nat.eq_dec (f h) (function_range f t)
  end.

Definition hash_function_range (h: hash_map) : (set nat) :=
  (function_range (hash_function h) (hash_input h)).

Definition set1 : set nat := 1 :: 2 :: nil.
Definition set2 := set_add Nat.eq_dec 1 set1.
Compute length set2.

Lemma adding_an_element_not_in_set_increases_cardinality:
  forall (s: set nat) (n: nat), (set_mem Nat.eq_dec n s) = false ->
    (length s) + 1 = length (set_add Nat.eq_dec n s).
Proof.
  intros. induction s.
  - reflexivity.
  - destruct (Nat.eq_dec n a) eqn:B.
    + unfold set_mem in H. rewrite e in H. simpl in H. destruct (Nat.eq_dec a a).
      * discriminate.
      * unfold not in n0. assert (a = a -> True). reflexivity. contradiction.
    + unfold set_add. rewrite B. simpl. assert (set_mem Nat.eq_dec n s = false) as C.
      * unfold set_mem. unfold set_mem in H. destruct (Nat.eq_dec n a).
        ** contradiction.
        ** apply H.
      * apply IHs in C. rewrite C. reflexivity.
Qed.
  
Inductive unique_set : set nat -> Prop :=
  | unique_set_empty : unique_set (empty_set nat)
  | unique_set_add (n : nat) (s : set nat) (H : unique_set s): unique_set (set_add Nat.eq_dec n s) 
  | unique_set_rem (n : nat) (s : set nat) (H : unique_set s): unique_set (set_remove Nat.eq_dec n s).

Lemma unique_set_preserves_uniqueness:
  forall (s: set nat), (unique_set s) -> NoDup s.
Proof.
  intros. induction H. 
  - apply NoDup_nil.
  - apply set_add_nodup. apply IHunique_set.
  - apply set_remove_nodup. apply IHunique_set.
Qed.  

Lemma not_in_set_intro:
  forall (a b: nat) (x: set nat), ~ (a = b \/ set_In a x) -> ~set_In a (set_add Nat.eq_dec b x).
Proof.
  intros. unfold not. intros. apply set_add_elim in H0. contradiction. 
Qed.

(* If an element n is not in a set s and f is an injective function, 
   f(n) is not in f(s) *)
Lemma injective_func_preserves_not_in_set:
  forall (s: set nat) (n : nat) (f : function), 
  injective f -> (set_mem Nat.eq_dec n s) = false 
  -> (set_mem Nat.eq_dec (f n) (function_range f s)) = false.
  intros. induction s.
  - reflexivity.
  - assert (set_mem Nat.eq_dec (f n) (function_range f s) = false).
    * apply set_mem_complete1 in H0. apply not_in_cons in H0. destruct H0.
      assert (set_mem Nat.eq_dec n s = false). apply set_mem_complete2. apply H1.
      apply IHs in H2. apply H2.
    * unfold function_range. fold function_range. apply set_mem_complete2. apply not_in_set_intro. 
      unfold not. apply <- Decidable.not_or_iff. split.
      ** assert (n <> a).
        *** unfold not. intros. apply set_mem_complete1 in H0. 
            unfold set_In in H0. rewrite H2 in H0. apply not_in_cons in H0. 
            destruct H0. unfold not in H0. apply H0. reflexivity. 
        *** unfold injective in H. intros. apply H in H3. contradiction.
      ** intros. apply set_mem_complete1 in H1. contradiction.
Qed. 

(* If f is a is an injective function and s is a unique set, then
  |f(s)| = |s|. *)
Lemma injective_func_leads_to_no_collisions:
  forall (f: function) (s : set nat), injective f -> unique_set s -> length s = length (function_range f s).
Proof.
  intros. induction s.
  - reflexivity.
  - unfold function_range. fold function_range. simpl. 
    assert ((set_mem Nat.eq_dec (f a) (function_range f s)) = false).
    + assert ((set_mem Nat.eq_dec a s) = false).
      * apply set_mem_complete2. unfold set_In. apply unique_set_preserves_uniqueness in H0.
        apply NoDup_cons_iff in H0. destruct H0. apply H0.
      * apply injective_func_preserves_not_in_set. apply H. apply H1.
    + apply adding_an_element_not_in_set_increases_cardinality in H1. rewrite <- H1. 
    assert (set_remove Nat.eq_dec a (a :: s) = s).
      * unfold set_remove. destruct (Nat.eq_dec a a). reflexivity. contradiction.  
      * assert (unique_set ( set_remove Nat.eq_dec a (a :: s))). 
        apply unique_set_rem. apply H0. rewrite H2 in H3. apply IHs in H3. lia.
Qed.

(* TODO: Defined injective hash map: input is set and function is injective. *)
