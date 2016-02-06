(** * 6.887 Formal Reasoning About Programs, Spring 2016 - Pset 0 *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

(* This lightweight pset is meant to force you to get started installing Coq
 * and finding bugs in our homework-submission system!  *ahem*  We meant
 * "learning to use our homework-submission system." ;-) *)

(* The Coq standard library contains a definition of a type of lists, a common
 * concept in functional programming.  More mainstream languages might call such
 * a thing an "immutable, singly linked list."
 *
 * Here's the type definition, which is effectively included automatically,
 * by default, in any Coq file.
 * <<
     Inductive list A :=
       nil
     | cons (hd : A) (tl : list A).
   >>
 *
 * [A] is a type parameter.  (Note that, following Coq's code-documentation
 * conventions, we put square brackets around bits of code within comments,
 * and we use double-angle brackets to set off larger code excerpts.)
 * This list type is a lot like the syntax-tree types we saw in class;
 * the only new wrinkle is the polymorphic type parameter [A], which is
 * related to *generics* in OO languages.
 *
 * We can also define some useful operations on lists.
 * A basic one is length.
 * <<
    Fixpoint length {A} (xs : list A) : nat :=
      match xs with
        | nil => 0
        | cons _ xs' => 1 + length xs'
      end.
   >>
 * Note the use of the natural-number type [nat].
 * The curly braces in type argument [{A}] tell Coq to infer this type argument
 * when [length] is called, which by the way is the default behavior for all
 * type arguments in Haskell and OCaml.
 * Another function is concatenation of lists, defined using an infix operator
 * [::] for [cons].
 * <<
    Fixpoint app {A} (l : list A) (m : list A) : list A :=
      match l with
       | nil => m
       | a :: l1 => a :: app l1 m
      end.
   >>
 * Finally, we'll also work with list reversal, using [++] as an infix operator
 * for [app].
 * <<
    Fixpoint rev {A} (l : list A) : list A :=
      match l with
        | nil => nil
        | x :: l' => rev l' ++ (x :: nil)
      end.
   >>
 *)

(* Here's an example proof with lists, using a list shorthand notation. *)
Theorem an_important_theorem : length [1; 2; 3] = 3.
Proof.
  simplify.
  equality.
Qed.


(* OK, enough warmup.  Your job is to define a module implementing the following
 * signature.  We ask you to implement a file Pset0.v, such that it can
 * be checked against this signature by successfully processing a third
 * file with a command like so:
 * <<
    Require Pset0Sig Pset0.

    Module M : Pset0Sig.S := Pset0.
   >>
 * You'll need to build your module first.  Here's the UNIX-style approach
 * that we'll use for grading: Put this file Pset0Sig.v, your solution
 * Pset0.v, and an additional file Pset0Check.v in some directory.
 * The last file should include the two lines of code quoted above.
 * Then create a _CoqProject file in the same directory, containing:
 * <<
-R ../../frap Frap
Pset0Sig.v
Pset0.v
Pset0Check.v
   >>
 * Replace the `../../frap' with the path to the unpacked book source.
 * Then create a Makefile with this content:
 * <<
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
   >>
 * If your Coq installation is set up properly, simply running `make' should
 * now be enough to build everything and check that it works.
 * Note also that you will need to run `make coq' in the directory of the book
 * library code, *before* starting to work on your solution, which needs
 * to import compiled library code from the book.
*)

(* Finally, here's the actual signature to implement. *)
Module Type S.
  Axiom another_important_theorem : length [1; 2; 3] = 1 + length [4; 5].

  Axiom length_concat : forall A (xs ys : list A), length (xs ++ ys) = length xs + length ys.
  (* Hint: want induction for this one! *)

  Axiom length_rev : forall A (xs : list A), length xs = length (rev xs).
  (* Hint: appeal to [length_concat] somewhere! *)
End S.

(* Example template for the Pset0.v file you will create:
 * <<
Require Import Frap.

Theorem another_important_theorem : length [1; 2; 3] = 1 + length [4; 5].
Proof.
  ...
Qed.

Theorem length_concat : forall A (xs ys : list A), length (xs ++ ys) = length xs + length ys.
Proof.
  ...
Qed.

Theorem length_rev : forall A (xs : list A), length xs = length (rev xs).
Proof.
  ...
Qed.
   >> *)
