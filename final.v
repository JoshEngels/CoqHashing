(* Inductive variable: Type :=
  | Var: nat -> variable. *)

(* TODO: Change hashmap to take in any object using polymorphism *)
Require Import Coq.Lists.ListSet.
Require Import List.
Require Import Coq.Arith.Arith.
Require Coq.Arith.PeanoNat.
From Coq Require Import Lia.


(* Had to copy the below from the standard library since couldn't import *)
(* -------------------------------------------------------------------------- *)
(** Remove by filtering *)
Definition remove' (x : nat) : list nat -> list nat :=
  filter (fun y => if Nat.eq_dec x y then false else true).

Lemma remove_alt (x : nat) (l : list nat) : remove' x l = remove Nat.eq_dec x l.
Proof with intuition.
  induction l...
  simpl. destruct Nat.eq_dec; f_equal...
Qed.

(** Counting occurrences by filtering *)

Definition count_occ' (l : list nat) (x : nat) : nat :=
  length (filter (fun y => if Nat.eq_dec y x then true else false) l).

Lemma count_occ_alt (l : list nat) (x : nat) :
  count_occ' l x = count_occ Nat.eq_dec l x.
Proof with intuition.
  unfold count_occ'. induction l...
  simpl; destruct Nat.eq_dec; simpl...
Qed.

Lemma in_remove: forall l x y, In x (remove Nat.eq_dec y l) -> In x l /\ x <> y.
Proof.
  intro l; induction l as [|z l IHl]; intros x y Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct (Nat.eq_dec y z) as [Heq|Hneq]; subst; split.
    + right; now apply IHl with z.
    + intros Heq; revert Hin; subst; apply remove_In.
    + inversion Hin; subst; [left; reflexivity|right].
      now apply IHl with y.
    + destruct Hin as [Hin|Hin]; subst.
      * now intros Heq; apply Hneq.
      * intros Heq; revert Hin; subst; apply remove_In.
Qed.

Lemma NoDup_filter:
  forall (f: nat -> bool) (l: list nat), NoDup l -> NoDup (filter f l).
Proof.
  induction l as [|a l IHl]; simpl; intros Hnd; auto.
  apply NoDup_cons_iff in Hnd.
  destruct (f a); [ | intuition ].
  apply NoDup_cons_iff; split; [intro H|]; intuition.
  apply filter_In in H; intuition.
Qed.

(* -------------------------------------------------------------------------- *)

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

Definition hash_output (h: hash_map) : (set nat) :=
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

(* If f is an injective function and s is a unique set, then
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

Definition num_collisions (h: hash_map) := length (hash_input h) - length (hash_output h).

Theorem injective_hash_map_on_set_no_collisions:
  forall (h: hash_map), (injective (hash_function h)) -> (unique_set (hash_input h))
    -> num_collisions h = 0.
Proof.
  intros. unfold num_collisions. assert (length (hash_input h) = length (hash_output h)). 
  apply injective_func_leads_to_no_collisions. apply H. apply H0.
  lia.
Qed.

(* From here on we stop focusing on ijective changes *)
Definition range_change (f : function) (n_in n_out: nat):= forall a, a < n_in -> f a < n_out.

Definition identity (n: nat) :=
  match n with
    | a => a
  end.

Lemma identity_preserves_identity:
  forall x, identity x = x.
Proof.
  intros. destruct x. reflexivity. reflexivity. 
Qed.

(* Identity function preserves range *)
Lemma identity_func_preserves_range:
  forall (n: nat), range_change identity n n.
Proof.
  intros. unfold range_change. intros. destruct n. 
  - lia.  
  - unfold identity. destruct a.
    + apply H.
    + apply H.
Qed.

Definition mod_func k n :=
  match n with
    | a => n mod k
  end.


Require Import Coq.Numbers.Integer.Abstract.ZDivEucl.
(* Mod function range is mod value *)
Lemma K_mod_func_changes_range_to_k:
  forall (modulus: nat) (n: nat), modulus > 0 -> range_change (mod_func modulus) n modulus.
Proof.
  intros. unfold range_change. intros. unfold mod_func. destruct a. 
  - destruct modulus.
    + lia.
    + simpl. lia.
  - assert (modulus <> 0). lia. apply Nat.mod_upper_bound. apply H1.
Qed. 

Definition composed_funcs (f g: function) (n: nat) :=
  match n with
    | a => (f (g a))
  end.

Definition modded_hash_map (h: hash_map) (m: nat) :=
  hash (composed_funcs (mod_func m)(hash_function h)) (hash_input h) .

(* Introduce the idea of bounding functions and a modded hash map *)
Definition function_bound (f: function) (n: nat) := forall m: nat, f m < n.

Lemma mod_func_bound:
  forall (m: nat), (m > 0) -> function_bound (mod_func m) m.
Proof.
  unfold function_bound. intros. unfold mod_func. apply Nat.mod_upper_bound. lia.
Qed.  

Lemma composition_preserves_bound:
  forall (f g: function) (n: nat), 
  function_bound f n -> function_bound (composed_funcs f g) n.
Proof.
  intros. unfold function_bound. intros. unfold composed_funcs. 
  unfold function_bound in H. apply H.
Qed. 


(* Filters with opposite values means sum preserves length *)
Lemma sum_length_opposite_filters_preserves_length:
  forall (l: list nat) (f g: nat -> bool), 
    (forall n: nat, f n = negb (g n)) -> length (filter f l) + length (filter g l) = length l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. destruct (f a) eqn:H0.
    + simpl. specialize (H a). rewrite H0 in H.  destruct (g a). 
      * discriminate.
      * lia.
    + simpl. specialize (H a). rewrite H0 in H.  destruct (g a). 
      * simpl. lia.
      * discriminate.
Qed. 


Require Import Coq.Lists.List.
(* Count of number of elements removed plus length of original list is length
of original length *)
Lemma sum_length_remove_preserves_length:
  forall (l: list nat) (n: nat),
    length (remove Nat.eq_dec n l) + (count_occ Nat.eq_dec l n) = length l.
Proof.
  intros. rewrite <- remove_alt. rewrite <- count_occ_alt. 
  unfold remove'. unfold count_occ'. apply sum_length_opposite_filters_preserves_length.
  intros. destruct (Nat.eq_dec n n0).
  - destruct (Nat.eq_dec n0 n). reflexivity. rewrite e in n1. contradiction.
  - destruct (Nat.eq_dec n0 n). rewrite e in n1. contradiction. reflexivity. 
Qed.

Definition list_bound (l: list nat) (m: nat) := forall (n: nat), (In n l) -> n < m.

Require Import Coq.Lists.List.

(* If a set is a unique set and bounded? (do the proof to figure out condition) 
   then it has at most length equal to the bound *)
Lemma set_bound_is_max_length:
  forall (m: nat) (s: set nat), (NoDup s) -> (list_bound s m) -> length s <= m.
Proof.
  induction m.
  - intros. unfold list_bound in H0. induction s.
    + reflexivity.
    + specialize (H0 a). simpl in H0. assert (~(a < 0)). lia. apply H1 in H0. lia. lia.
  - intros. assert (list_bound (remove Nat.eq_dec m s) m).
    + unfold list_bound. intros. apply in_remove in H1. destruct H1. 
      unfold list_bound in H0. specialize (H0 n). apply H0 in H1. lia.
    + assert (NoDup (remove Nat.eq_dec m s)).
      * rewrite <- remove_alt. unfold remove'. apply NoDup_filter. apply H. 
      * specialize (IHm (remove Nat.eq_dec m s)). apply IHm in H2.
        ** assert ((length (remove Nat.eq_dec m s)) + (count_occ Nat.eq_dec s m) = length s).
          *** apply sum_length_remove_preserves_length.
          *** rewrite <- H3. assert (count_occ Nat.eq_dec s m <= 1).
            **** apply NoDup_count_occ. apply H.
            **** lia. 
        ** apply H1.
Qed.

Lemma function_bound_implies_list_bound:
  forall (f: function) (l: list nat) (m: nat),
  (function_bound f m) -> (list_bound (function_range f l) m).
Proof.
  intros. induction l.
  - easy.
  - unfold list_bound. unfold list_bound in IHl. unfold function_range. fold function_range.
    intros. apply  set_add_elim in H0. destruct H0.
    + unfold function_bound in H. specialize (H a). rewrite H0. apply H.
    + specialize (IHl n). apply IHl. apply H0.
Qed.


(* If a function has a max, the range of the function on any list is less than 
   than the max. *)
Lemma function_range_max_size:
  forall (f: function) (l: list nat) (max: nat), 
  (function_bound f max) -> (length (function_range f l)) <= max.
Proof.
  intros. assert (unique_set (function_range f l)).
  - induction l.
  + simpl. apply unique_set_empty.
  + unfold function_range. apply unique_set_add. unfold function_range in IHl. apply IHl. 
  - apply set_bound_is_max_length. apply unique_set_preserves_uniqueness in H0. apply H0. apply function_bound_implies_list_bound. apply H.
Qed.
  
(* Best case number of hash collisions for any hash function:
   If we have a modded hash map to length l, and the hash input is of length k,
   then there >= k - l collisions.
*)
Theorem best_case_hash_map_num_collisions:
  forall (h: hash_map) (output_length: nat), 
  output_length > 0 -> num_collisions (modded_hash_map h output_length) >= 
  (length (hash_input h)) - output_length.
Proof.
  intros. unfold num_collisions. simpl. 
  assert (length (hash_output (modded_hash_map h output_length)) <= output_length).
  - unfold modded_hash_map. unfold hash_output.
    assert (function_bound (hash_function
    (hash (composed_funcs (mod_func output_length) (hash_function h))
       (hash_input h))) output_length).
    + apply composition_preserves_bound. apply mod_func_bound. apply H.
    + apply function_range_max_size. apply H0. 
  - lia.


(* Some fun examples *)
Import ListNotations.
Definition squared (n: nat) := n * n.
Definition hash_map_1 := hash (squared) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Definition hash_map_1_mod := (modded_hash_map hash_map_1 11).
Compute (num_collisions hash_map_1_mod).
