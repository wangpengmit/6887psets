(** * 6.887 Formal Reasoning About Programs - Lab 13
    * Using Message Passing to Implement Objects *)

Require Import Frap Frap.MessagesAndRefinement.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Before it went mainstream, object-oriented programming was conceptualized in
 * terms of processes exchanging messages amongst themselves.  Each method call
 * is a message.  We can make this perspective concrete in the process algebra
 * from class.  BTW, to process the code in this file without needing to rebuild
 * all the frap code, we suggest running the following in the 'frap' directory:
 *   make MessagesAndRefinement.vo
 *)


(* Here's a function that produces a process, given parameters equivalent to a
 * standard definition of an object from object-oriented programming. *)
Definition object (state method result : Set)
           (* First, a few type parameters, explained below by how they are
            * used. *)

           (initialState : state)
           (* This is the initial value of the object's private state, which you
            * can think of like private fields in Java. *)

           (handle : method -> state -> state * result)
           (* When a method is called, we use this function to compute the new
            * state and the method return value, respectively. *)

           (input output : channel)
           (* In process land, method calls come in on the [input] channel, with
            * return values sent back on the [output] channel. *)
  :=
  New[input;output](st);
  (!!st(initialState); Done)
  || Dup (??st(s : state);
          ??input(m : method);
          let (s', r) := handle m s in
          !!output(r);
          !!st(s');
          Done).
(* Note the twisty thing being done by the code above: private channel [st]
 * stands in for a mutable field!  The current "value" of that field is whatever
 * value is being sent (internally) to [st].  Note that this is our first
 * example of a [Dup] with threads that will communicate with each other
 * directly. *)

(* Given a list of method calls, we can send them one after another to a
 * channel. *)
Fixpoint callMethods (method : Set) (input : channel) (ms : list method) :=
  match ms with
  | nil => Done
  | m :: ms' =>
    !!input(m);
    callMethods input ms'
  end.

(* Here's a more straightforward way of running a sequence of method calls,
 * sending their return values as output. *)
Fixpoint runMethods (state method result : Set) (s : state)
         (handle : method -> state -> state * result)
         (output : channel) (ms : list method) :=
  match ms with
  | nil => Done
  | m :: ms' =>
    let (s', r) := handle m s in
    !!output(r);
    runMethods s' handle output ms'
  end.

(* Now, your challenge for today: prove that any behavior of the simple way of
 * running methods can be matched by the fancy object encoding, where we run a
 * method-caller thread in parallel with the object. *)
Theorem object_ok : forall (state method result : Set)
                           (initialState : state)
                           (handle : method -> state -> state * result)
                           input output ms,
    input <> output
    -> runMethods initialState handle output ms
       <| Block input; callMethods input ms || object initialState handle input output.
Proof.
Admitted.
