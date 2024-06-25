Require Import Arith.
Require Import List.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Classical.
Import ListNotations.

Inductive Direction : Set := input | output.

Definition Id : Type := nat.

Inductive System : Type :=
  | system : Id -> System
  | comp_system : list Component -> System -> System
with Component : Type :=
  | component : Id -> Component
  | comp_component : list Component -> Component -> Component
  | func_component : list Function -> Component -> Component
with Function : Type :=
  | function : Id -> Function
  | dflow_function : DirectedFlow -> Function -> Function
with DirectedFlow : Type :=
  | directedflow : Id -> DirectedFlow
  | pflow_directedflow : PhysicalFlow -> Direction -> DirectedFlow -> DirectedFlow
with PhysicalFlow : Type :=
  | physicalflow : Id -> PhysicalFlow.

Definition steam := physicalflow 0.

Definition water := physicalflow 1.

Definition circuit := func_component 
[
dflow_function (pflow_directedflow steam input (directedflow 0)) (function 0);
dflow_function (pflow_directedflow water output (directedflow 0)) (function 1)
]
(component 0).

Definition drying_block := func_component
[
dflow_function (pflow_directedflow steam output (directedflow 0)) (function 2)
]
(component 1).

Definition inlet := func_component
[
dflow_function (pflow_directedflow water input (directedflow 0)) (function 3)
]
(component 2).

Definition steam_generator := comp_system
[
circuit;
drying_block;
inlet
]
(system 0).



Fixpoint get_directed_flows_func (f : Function) : list DirectedFlow :=
  match f with
  | function _ => []
  | dflow_function df f' => df :: get_directed_flows_func f'
  end.

Fixpoint get_directed_flows_comp (c : Component) : list DirectedFlow :=
  match c with
  | component _ => []
  | comp_component cs c' => concat (map get_directed_flows_comp cs) ++ get_directed_flows_comp c'
  | func_component fs c' => concat (map get_directed_flows_func fs) ++ get_directed_flows_comp c'
  end.

Fixpoint get_directed_flows_system (s : System) : list DirectedFlow :=
  match s with
  | system _ => []
  | comp_system cs s' => concat (map get_directed_flows_comp cs) ++ get_directed_flows_system s'
  end.


Fixpoint containsDirectedFlow (p : PhysicalFlow) (d : Direction) (df : DirectedFlow) : Prop :=
  match df with
  | directedflow _ => False
  | pflow_directedflow p' d' df' => (p = p' /\ d = d') \/ containsDirectedFlow p d df'
  end.


Fixpoint containsDirectedFlow_List (p : PhysicalFlow) (d : Direction) (dfs : list DirectedFlow) : Prop :=
  match dfs with
  | [] => False
  | (pflow_directedflow p' d' df) :: dfs' => (p = p' /\ d = d') \/ (containsDirectedFlow_List p d dfs') \/ (containsDirectedFlow p d df)
  | _ :: dfs' => containsDirectedFlow_List p d dfs'
  end.

Definition ConsumedFlowsAllProduced (s : System) : Prop :=
  forall (p: PhysicalFlow), containsDirectedFlow_List p input (get_directed_flows_system s) -> containsDirectedFlow_List p output (get_directed_flows_system s).

Definition ProducedFlowsAllConsumed (s : System) : Prop :=
  forall (p: PhysicalFlow), containsDirectedFlow_List p output (get_directed_flows_system s) -> containsDirectedFlow_List p input (get_directed_flows_system s).

Goal (ConsumedFlowsAllProduced steam_generator).
Proof.

(* Explicit Declaration of Simple Identities with proof by tautology *)

assert (impl_ident : forall p q : Prop, (p -> q) <-> ((~p) \/ q)).
{ intros. tauto. }

assert (neg_disj_ident : forall p q : Prop, ~ (p \/ q) <-> (~p) /\ (~q)).
{ intros. tauto. }

assert (excluded_middle_1 : forall p : Prop, p \/ ~p <-> True).
{ intros. tauto. }

assert (excluded_middle_2 : forall p : Prop, ~p \/ p <-> True).
{ intros. tauto. }

assert (lor_refl : forall p q : Prop, (p \/ q) <-> (q \/ p)).
{ intros. tauto. }

assert (lor_false : forall p : Prop, (p \/ False) <-> p).
{ intros. tauto. }

assert (false_lor : forall p : Prop, (False \/ p) <-> p).
{ intros. tauto. }

assert (lor_true : forall p : Prop, (p \/ True) <-> True).
{ intros. tauto. }

assert (true_lor : forall p : Prop, (True \/ p) <-> True).
{ intros. tauto. }

assert (and_false : forall p : Prop, (p /\ False) <-> False).
{ intros. tauto. }

assert (false_and : forall p : Prop, (False /\ p) <-> False).
{ intros. tauto. }

assert (and_true : forall p : Prop, (p /\ True) <-> p).
{ intros. tauto. }

assert (true_and : forall p : Prop, (True /\ p) <-> p).
{ intros. tauto. }

assert (input_is_input: input = input <-> True).
{ intros. tauto. }

(* Explicit Declaration of inequality identities using contradiction *)

assert (input_not_output: (input = output <-> False)).
{ split. discriminate. contradiction. }

assert (output_not_input: (output = input <-> False)).
{ split. discriminate. contradiction. }

assert (output_is_output: output = output <-> True).
{ intros. tauto. }

(* Actual proof begins *)
(* Introduce premise and goal *)
intro.
(* Apply functions to simply goal *)
simpl.

(* Introduce simple propositions for fluid values *)
remember (p = steam) as P.
remember (p = water) as Q.

(* Apply simple equality identities *)
rewrite input_is_input.
rewrite input_not_output.
rewrite output_not_input.
rewrite output_is_output.

(* Apply logical operator identities *)
repeat rewrite false_lor.
repeat rewrite lor_false.
repeat rewrite and_true.
repeat rewrite and_false.
repeat rewrite false_lor.
repeat rewrite lor_false.
repeat rewrite neg_disj_ident.

(* Finally apply relfexivity of logical OR *)
(* Separate antecedent and consequent *)
intros Ant.
(* Utilize reflexivity of logical OR *)
apply lor_refl.
(* Apply antecedent to trivally prove consequent *)
apply Ant.
Qed.
(* Proof finished*)

Goal (ProducedFlowsAllConsumed steam_generator).
Proof.
(* Simple tautology without explicit declarations of identities used *)
intro. 
simpl. 
tauto. 
Qed.
(* Proof finished*)





