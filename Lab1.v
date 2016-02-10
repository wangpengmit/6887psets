(** * 6.887 Formal Reasoning About Programs - Lab 1
    * Relational Algebra: Semantics and Optimization *)

Require Import Frap.

(* Authors: Adam Chlipala (adamc@csail.mit.edu), Peng Wang (wangpeng@csail.mit.edu) *)

(* *Relational algebra* is the formalism underlying database systems like SQL.
 * In this lab, we'll formalize a subset of relational algebra and prove the
 * correctness of some analyses and transformations on it, similar to those that
 * might appear in an SQL query optimizer. *)

(* The basic unit is a *relation*, essentially a set of records with named
 * fields, with each field storing a number. *)
Definition row := list (var * nat). (* That asterisk is for a pair type. *)
Definition relation := list row.

(* Here's a classic example of the sort found in databases textbooks the world
 * over. *)
Example employees : relation :=
  [[("EmployeeID", 12); ("Salary", 200); ("Department", 3)];
    [("EmployeeID", 37); ("Salary", 500); ("Department", 5)];
    [("EmployeeID", 58); ("Salary", 320); ("Department", 3)]].
Example departments : relation :=
  [[("DepartmentID", 3); ("FloorNumber", 37)];
    [("DepartmentID", 5); ("FloorNumber", 18)]].
(* Each employee has an ID, a salary, and a department.
 * Employees reference their departments by department ID.
 * A separate relation gives information on departments by ID, in this case the
 * floor of the building for the department. *)

(* Here's a helpful function for looking up one named field of a row. *)
Fixpoint lookup (rw : row) (x : var) : nat :=
  match rw with
  | nil => 0
  | (y, n) :: rw' => if x ==v y then n else lookup rw' x
  end.

(* Now to start defining the syntax of relational algebra.
 * We begin with numerical expressions. *)
Inductive nexp :=
| Const (n : nat)
| Field (fieldname : var).

(* Next, we have Boolean expressions. *)
Inductive bexp :=
| Truth
| Equal (ne1 ne2 : nexp)
| And (be1 be2 : bexp).

(* Finally, a type of relational expressions.
 * We'll explain these constructs by example shortly. *)
Definition projection := list var.
Inductive rexp :=
| Var (rx : var)
| Project (re : rexp) (pr : projection)
| Filter (re : rexp) (be : bexp)
| Join (re1 re2 : rexp).

(* Now some notation magic, to make our examples more palatable! *)
Coercion Const : nat >-> nexp.
Coercion Field : var >-> nexp.
Infix "=" := Equal : bexp_scope.
Infix "&&" := And : bexp_scope.
Delimit Scope bexp_scope with bexp.
Coercion Var : var >-> rexp.
Notation "re 'keeping' pr" := (Project re pr) (at level 80).
Notation "re 'where' be" := (Filter re be%bexp) (at level 80).
Infix ",," := Join (at level 80).

(* Here's an example showing all the features. *)
Example peopleOnFloors :=
  "Employees",, "Departments"
    (* First, we name the two relations and *join* them together in a Cartesian
     * product, generating the concatenation of every pair of records. *)
  where "Department" = "DepartmentID"
    (* Next, we *filter*, keeping only the pairs where the department IDs
     * agree. *)
  keeping ["EmployeeID"; "FloorNumber"].
    (* Finally, we *project*, throwing away all but two of the columns. *)
(* What does this *query* do?  It returns a relation associating each employee
 * (by ID) with the floor number of his or her department. *)

(* CHALLENGE #1: Implement an interpreter for [rexp], probably using the
 * following type, which can play a similar role to that of the variable valuation
 * in our examples from the prior lecture. *)
Definition relations := list (var * relation).

(* And here's our example database in that form: *)
Definition database : relations := [("Employees", employees);
                                     ("Departments", departments)].

(* And here's a [relations] lookup function to start you off. *)
Fixpoint rlookup (rs : relations) (x : var) : relation :=
  match rs with
  | nil => nil
  | (y, r) :: rs' => if x ==v y then r else rlookup rs' x
  end.

(* Finally, this guy might be a helpful time saver. *)
Definition join (r1 r2 : relation) : relation :=
  flat_map (fun rw1 => map (fun rw2 => rw1 ++ rw2) r2) r1.
(* To understand what is going on, see the definitions of the ingredients,
 * which get printed using an anonymous form [fix] of recursive function
 * definitions.  We'll include a third one here that isn't actually used above,
 * but which is likely to come in handy. *)
Print map.
Print flat_map.
Print filter.
(* Remember that [++] is list concatenation.
 * We also have the usual Boolean operators available with the type [bool].
 * Beside [true] and [false], we have infix [&&] and [||].
 * Also handy will be infix operator [==n] for comparing numbers for equality.
 * It doesn't quite have [bool] type, so you may want to use it like this:
 * [if E1 ==n E2 then true else false].
 * One last suggestion: the tactic form [rewrite <- H] may be helpful, for using
 * an equality in the right-to-left direction for rewriting. *)


(* CHALLENGE #2: implement and prove correct a simple optimization, based on
 * this law of relational algebra: *)
Definition claimedLaw := forall re be1 be2, (re where be1 where be2) = (re where be1 && be2).
(* There are many more laws where that one came from, and SQL database engines
 * implement them in efficient ways! *)


(* CHALLENGE #3: implement and prove correct a kind of type-checker for [rexp]s,
 * returning its *schema*, defined like so: *)
Definition row_schema := list var.
Definition schema := list (var * row_schema).
(* A [row_schema] explains which field names are available.
 * That's the right type to use for the type-checker output.
 * A [schema] explains which relations exist and what is the schema of each.
 * You probably want to write your type-checker to accept a [schema] as input,
 * along with the [rexp] to check. *)

(* And here's a schema lookup function for free! *)
Fixpoint slookup (sc : schema) (x : var) : row_schema :=
  match sc with
  | nil => nil
  | (y, rsc) :: sc' => if x ==v y then rsc else slookup sc' x
  end.

(* Formulating the correctness condition is part of the challenge, but we
 * suggest using the following definitions, which return elements of the type
 * [Prop] of truth values, which can be built with "constants" [True] and
 * [False], as well as usual propositional operators like conjunction [/\].
 * Quick explanation of why [Prop] instead of [bool]: the latter is for
 * executable program stuff, while the former exists in the relatively flexible
 * world of math. *)

Fixpoint rowOk (rw : row) (rsc : row_schema) : Prop :=
  match rw, rsc with
  | nil, nil => True
  | (fn, n) :: rw', fn' :: rsc' => fn = fn' /\ rowOk rw' rsc'
  | _, _ => False
  end.

Fixpoint relationOk (r : relation) (rsc : row_schema) : Prop :=
  match r with
  | nil => True
  | rw :: r' => rowOk rw rsc /\ relationOk r' rsc
  end.

Fixpoint relationsOk (rs : relations) (sc : schema) : Prop :=
  match rs, sc with
  | nil, nil => True
  | (rn, r) :: rs', (rn', rsc) :: sc' =>
    rn = rn' /\ relationOk r rsc /\ relationsOk rs' sc'
  | _, _ => False
  end.

(* Some more tactic tips for the proof:
 * Consider using the [cases] tactic on any variable of a composite type,
 * as in the pair types used above.
 * Also consider a new tactic [propositional] that simplifies uses of the
 * propositional connectives like [/\].  (It also knows how to prove any goal,
 * given a contradictory hypothesis of [False].)
 * As usual, expect to prove plenty of lemmas, one per induction in the
 * proof! *)


(* CHALLENGE #4: Implement and prove correct an optimization that pushes parts
 * of filter conditions through joins, where those parts only depend on fields
 * coming from one side of the join.  For example, we want to generate the
 * second query from the first: *)
Definition original := "Employees",, "Departments"
                       where (("EmployeeID" = 7) && ("Department" = "DepartmentID")).
Definition optimized := ("Employees" where "EmployeeID" = 7),, "Departments"
                        where "Department" = "DepartmentID".
(* What makes this change an "optimization"?  The filter on employee ID can be
 * performed on the employee table alone, rather than on the cross-product table
 * between employees and departments, which can be asymptotically larger, as the
 * input relations grow.
 * We recommend implementing a simplified version of this transformation.
 * For one thing, we suggest not implying it recursively.  That is, don't apply
 * the same law to simplify within subterms of a spot where the law itself
 * applies.  Also, we suggest restricting attention to pulling out part of a
 * filter condition that can apply to the first argument of a join, though it
 * is also possible to pull conditions to the right argument or to both.
 * WARNING: this is a quite nontrivial exercise, included to make sure no one
 * runs out of things to do. ;-)  Our solution runs to about 200 lines. *)
