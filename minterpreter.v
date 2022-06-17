(* External Libraries*)
Require Import bbv.Word.

(* Standard Libraries *)
Require Import Arith.
Require Import Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.NArith.NArith.
Require Export Coq.Strings.String.
Require Export Coq.Strings.Ascii.
Require Import Nat.
Require Import List.
Import ListNotations.

(* Notations *)

Notation "m '=?n' n" := (m =? n) (* nat equality *)
  (at level 100).

Notation "s '=?s' t" := (Coq.Strings.String.eqb s t) (* string equality *)
  (at level 100).

(* Constant values *)
Definition WLen: nat := 256. 
Definition bigNum : N := wordToN (wlshift' (natToWord 257 1) 256).
Definition WZero := natToWord WLen 0.
Definition WTrue := natToWord WLen 1. 
Definition WFalse:= natToWord WLen 0.
Definition ByteLen: nat := 8.
Definition Byte := word ByteLen.


(* Arbitrary key and value map *)
Definition map' (K V: Type) : Type := K -> option V.

Definition empty_map' {K V: Type} : map' K V :=
  (fun _ => None).

Definition update' {K V : Type} (eqk: K -> K -> bool) (m : map' K V) (k: K) (v: V) :=
  fun k' => if eqk k k' then Some v else m k'.

(* Notation for string key map *)
Notation "x '|->s' v ';' m" := (update' Coq.Strings.String.eqb m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->s' v" := (update' Coq.Strings.String.eqb empty_map' x v)
  (at level 100).


(* string key map *)
Definition map (V: Type) : Type := string -> option V.

Definition empty_map {V: Type} : map V :=
  (fun _ => None).

Definition update {V : Type} (m : map V) (k: string) (v: V) :=
  fun k' => if k' =?s k then Some v else m k'.

(* Notation for string key map *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty_map x v)
  (at level 100).


Module Interpreter.

(** Here we define the values of the concrete machine we are
    working with. In our case, [val] will be defined as an
    [EVMWord], and [EVMWord] will be defined in term of [word WLen]
    ([WLen : nat := 256]).
    But for testing purposes, [val] is going to be defined as a [nat]*)

Definition EVMWord := word WLen.
(*Definition val := EVMWord.*)
Definition val := nat.

(** [instr] : EVM Opcodes (those which work over the stack).
    [operator]: Semantics of Opcodes that are not POP, PUSHk, DUPk, or SWAPk.
    [sfs_val]:  Values from a Stack Functional Specification (SFS):
      - (i)   A numeric value.
      - (ii)  A symbolic value si from S0, where S0 is the initial [symbolic_stack]
              we created the SFS from.
      - (iii) An expression of the form "op a1 a2 ... an" where ai is of type (iii).
    [asfs_val]: Value from Abstract Stack Functional Specification (ASFS):
      - (i)   A numeric value.
      - (ii)  A symbolic fresh value si, not contained in S0
*)

Inductive instr : Type :=
  | Pop
  | Push   (v : val)
  | Dup    (k : nat)
  | Swap   (k : nat)
  | OpCode (name : string).

Inductive operator : Type :=
  | Op  (nargs : nat) (func : list val -> val)
  | COp (func : val -> val -> val).

Inductive sfs_val : Type :=
  | SFSNum (n : val)
  | SFSVar (id : string)
  | SFSOp  (opcode : string) (args : list sfs_val).

Inductive asfs_val : Type :=
  | ASFSNum (n : val)
  | ASFSVar (id : string).
  
Definition prog := list instr. 
Definition concrete_stack := list val.
Definition symbolic_stack := list string.
Definition sfs  := list sfs_val.
Definition asfs := list asfs_val.
Definition asfs_map := map sfs_val.

(* Stack manipulation operators *)
Definition push {T : Type} (v : T) (sk : list T) : list T :=
  v :: sk.

Definition pop {T : Type} (sk : list T) : list T :=
  match sk with
  | x::sk' => sk'
  | _ => []
  end.

Definition dup {T : Type} (k : nat) (sk : list T) : list T :=
  match nth_error sk k with
  | None => []
  | Some x => x::sk
  end.

Definition swap {T : Type} (k : nat) (sk : list T) : list T :=
  (rev (firstn k sk)) ++ (skipn k sk).

(* Concrete evaluation *)

Definition concrete_eval' (ins: instr) (cs: concrete_stack) 
(ops: map operator): concrete_stack :=
  match ins with
  | Push v => push v cs
  | Pop => pop cs
  | Dup k => dup k cs
  | Swap k => swap k cs
  | OpCode name => match (ops name) with 
    | Some (Op nargs func) => (func (firstn nargs cs))::(skipn nargs cs)
    | Some (COp func) =>
      match cs with
      | n1::n2::cs' => (func n1 n2)::cs'
      | _ => []
      end
    | None => []
    end
  end.

Fixpoint concrete_eval (p : prog) (cs : concrete_stack) 
(ops : map operator) : concrete_stack :=
  match p with
  | [] => cs
  | inst::p' => concrete_eval p' (concrete_eval' inst cs ops) ops
  end.

(* SFS *)

Fixpoint concrete_to_sfs (ss : symbolic_stack) : sfs :=
  match ss with
  | nil => nil
  | s::ss' => (SFSVar s)::(concrete_to_sfs ss')
  end.

Definition generate_sfs' (ins: instr) (s: sfs) 
(ops: map operator) : sfs :=
  match ins with 
  | Push v      => push (SFSNum v) s
  | Pop         => pop s
  | Dup k       => dup k s
  | Swap k      => swap k s
  | OpCode name => match (ops name) with
                         | Some (Op nargs _) => 
                           (SFSOp name (firstn nargs s))::(skipn nargs s)
                         | Some (COp _) => match s with 
                                           | n1::n2::s' => (SFSOp name [n1; n2])::s'
                                           | _ => nil
                                          end
                         | None => nil
                         end
  end.

Fixpoint generate_sfs (p: prog) (s:sfs) (ops: map operator) : sfs :=
  match p with
  | nil => s
  | ins::p' => generate_sfs p' (generate_sfs' ins s ops) ops
  end.

(* Examples *)

Example p0 := [Push 1; Push 2].
Example p1 := [Push 1; Push 2;  OpCode "add"].
Example p2 := [OpCode "add"].

Example map0 : map operator := ("add" |-> COp (fun x => fun y => x+y)).
Example cs0 := [3; 2; 1].
Example cs2 := [3].

Example test0_concrete_eval: concrete_eval p0 cs0 map0 = [2;1;3;2;1].
Proof. cbv. reflexivity. Qed.

Example test1_concrete_eval: concrete_eval p1 cs0 map0 = [3;3;2;1].
Proof. unfold cs0. simpl. cbv. reflexivity. Qed.

Example test2_concrete_eval: concrete_eval p2 cs2 map0 = [].
Proof. cbv. reflexivity. Qed.

(* Example test0_generate_sfs: *) 
(* generate_sfs p0 (concrete_to_sfs ["s2"; "s1"; "s0"]) map0 = *)
(* [SFSNum 2; SFSNum 1; SFSVar "s2"; SFSVar "s1"; SFSVar "s0"]. *)
(* Proof. *) 
(*   unfold p0. *) 
(*   unfold concrete_to_sfs. unfold generate_sfs. unfold generate_sfs'. *) 
(*   unfold push. reflexivity. Qed. *)

(* Example test1_generate_sfs: *) 
(* generate_sfs p1 (concrete_to_sfs ["s2"; "s1"; "s0"]) map0 = *)
(* [(SFSOp "add" [SFSNum 2; SFSNum 1]); SFSVar "s2"; SFSVar "s1"; SFSVar "s0"]. *)
(* Proof. cbv. reflexivity. Qed. *)


End Interpreter.
