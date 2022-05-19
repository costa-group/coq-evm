(* Enrique Martin - Univ. Complutense de Madrid
   Licensed under the GNU GENERAL PUBLIC LICENSE 3.0.

   You may obtain a copy of the License at
   https://www.gnu.org/licenses/gpl-3.0.txt
*)


Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.Init.Nat. (* for <? *)

Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Open Scope string_scope.


Require Import Coq_EVM.lib.evmModel.
Require Import Coq_EVM.string_map.


(***********
  CONCRETE EVALUATION OF A PROGRAM WRT. A STACK
 ***********)
Definition infinite_gas : nat := 2048.

Definition empty_execution_state (stack: list (EVMWord)) : ExecutionState :=
  ExecutionStateMk stack 
                   (M.empty EVMWord)
                   (M.empty EVMWord)
                   (M.empty (list (word 8)))
                   0
                   nil.

Definition empty_callinfo : CallInfo := 
CallInfoMk nil 
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           nil
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (natToWord WLen 0)
           (M.empty EVMWord).
           

(* Add a STOP instruction at the end of the program so that evmModel does no generate a jump exception *) 
Definition concrete_eval (program: list OpCode) (stack: list (EVMWord)) : option (list EVMWord) :=
match actOpcode infinite_gas 0 (empty_execution_state stack) (app program (STOP::nil)) empty_callinfo with
| inr (SuccessfulExecutionResultMk execStat) => Some (getStack_ES execStat)
| inr (SuccessfulExecutionResultMkWithData execStat data) => None
  (* SuccessfulExecutionResultMkWithData should not be returned in our EVM blocks because it is
     generated with LOG, CREATE, CALL and CALLCODE instructions*)
| inl _ => None
end.
  
  
Compute (concrete_eval (SimplePriceOpcodeMk ADD::nil) 
         ((natToWord WLen 2)::(natToWord WLen 3)::(natToWord WLen 5)::nil)).




(**********
  SFS 
 **********)

Definition abstract_stack := list string.

Inductive sfs_val : Type :=
  | SFSconst (v: EVMWord)
  | SFSname (name: string)
  | SFSbinop (op: OpCode) (name1 name2: string).
  (* SFSuop & SFSterop for unary and ternary operations, if needed *)
  
Definition sfs_map := map sfs_val.

Inductive sfs : Type := 
  SFS (absi: abstract_stack) (abso: abstract_stack) (sfsmap: sfs_map).

(* Initial stack and SFS map contains disjoint symbols *)
Definition disjoint_stack_sfs (stack: map EVMWord) (csfs: sfs) : Prop :=
match csfs with 
  | SFS absi abso sfsmap => disjoint (domain stack) (domain sfsmap)
end.



(* Syntactic equality of Opcode (instructions) 
   TODO: extend to all possible instructions and prove equivalence with =:
         - (EVMoper_eqb i1 i2) = true <-> i1 = i2
         - (EVMoper_eqb i1 i2) = false <-> i1 <> i2
   *)
Definition EVMoper_eqb (i1 i2: OpCode) : bool :=
match (i1, i2) with
 | (STOP, STOP) => true
 | (RETURN, RETURN) => true
 | (ComplexPriceOpcodeMk op1, ComplexPriceOpcodeMk op2) => false (* Not supported *)
 | (SimplePriceOpcodeMk op1, SimplePriceOpcodeMk op2) => match (op1, op2) with
                                                          | (ADD, ADD) => true
                                                          | (MUL, MUL) => true
                                                          | (SUB, SUB) => true
                                                          | (PUSH arg1 w1, PUSH arg2 w2) => andb (weqb arg1 arg2) (weqb w1 w2)
                                                          | (POP, POP) => true
                                                          | _ => false
                                                         end
 | _ => false
end.



(* Recursive function for exact syntactic equality *)
Definition sfsval_eqb (sfs1 sfs2: sfs_val) : bool :=
match (sfs1, sfs2) with
 | (SFSconst v1, SFSconst v2) => weqb v1 v2
 | (SFSname name1, SFSname name2) => name1 =? name2
 | (SFSbinop op1 arg11 arg12, SFSbinop op2 arg21 arg22) => 
      andb (EVMoper_eqb op1 op2) 
           (andb (arg11 =? arg21) (arg12 =? arg22))
 | _ => false
end.





(*
(****************
 SFS equivalence [need to be adapted]
*****************)
Definition sfs_eq_symbol (d: nat) (symb1 symb2 : string) (map1 map2 : sfs_map) : bool :=
match (resolve_sfs_expr d (SFSname symb1) map1, resolve_sfs_expr d (SFSname symb2) map2) with
 | (None, _) => false
 | (_, None) => false
 | (Some sfs1, Some sfs2) => sfsval_eqb sfs1 sfs2
end.

Fixpoint sfs_eq_list (d: nat) (in1 in2 : abstract_stack) (map1 map2 : sfs_map) : bool :=
match in1 with 
 | nil => match in2 with
           | nil => true
           | _::_ => false
          end
 | v1::r1 => match in2 with
              | nil => false
              | v2::r2 => andb (sfs_eq_symbol d v1 v2 map1 map2) (sfs_eq_list d r1 r2 map1 map2)
             end
end.

Definition sfs_eqb (d: nat) (sfs1 sfs2 : sfs) : bool :=
match (sfs1, sfs2) with
 | (SFS in1 map1, SFS in2 map2) => sfs_eq_list d in1 in2 map1 map2
end.


(* Test: equivalent SFS *)
Compute (abstract_eval (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk POP::nil)).
Compute (abstract_eval (SimplePriceOpcodeMk POP::SimplePriceOpcodeMk POP::nil)).
Compute (
let prog1 := abstract_eval (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk POP::nil) in 
let prog2 := abstract_eval (SimplePriceOpcodeMk POP::SimplePriceOpcodeMk POP::nil) in 
match (prog1, prog2) with
 | (Some sfs1, Some sfs2) => Some (sfs_eqb 1024 sfs1 sfs2)
 | _ => None
end).

Compute (
let sfs1 := SFS ("s2"::"s3"::nil) (("e0",SFSbinop (SimplePriceOpcodeMk ADD) (SFSname "s0") (SFSname "s1"))::nil) in
let sfs2 := SFS ("e0"::"s3"::"s4"::nil) (("e0",SFSbinop (SimplePriceOpcodeMk SUB) (SFSname "s1")(SFSname "s2"))::nil) in
sfs_eqb 1024 sfs1 sfs2
).

(* Test: not equivalent SFS *)
Compute (abstract_eval (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk POP::nil)).
Compute (abstract_eval (SimplePriceOpcodeMk POP::SimplePriceOpcodeMk SUB::nil)).
Compute (
let prog1 := abstract_eval (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk POP::nil) in 
let prog2 := abstract_eval (SimplePriceOpcodeMk POP::SimplePriceOpcodeMk SUB::nil) in 
match (prog1, prog2) with
 | (Some sfs1, Some sfs2) => Some (sfs_eqb 1024 sfs1 sfs2)
 | _ => None
end).
*)



(***********************************
 EVALUATION OF AN SFS FROM A CONCRETE STACK 
 **********************************)
Definition evaluate_concrete_element (oper: OpCode) (args: list EVMWord) 
  : option EVMWord :=
(* relies on actOpcode, the EVM model function for evaluating programs. Here I construct an 
   ad-hoc program and stack and execute it inside an empty execution state and empty callinfo *)
match (actOpcode 1000 0 (empty_execution_state args) (oper::STOP::nil) empty_callinfo) with
 | inr (SuccessfulExecutionResultMk (ExecutionStateMk (e::_) _memory _storage _pc _contracts _)) => Some e
 | _ => None
end.


(* Dummy natural variable "d" for decreasingness *)
Fixpoint evaluate_sfs_from_map (d: nat) (concrete_stack: map EVMWord) (spec: sfs) (symbol: string)
  : option EVMWord :=
match d with
 | 0 => None
 | S d' => match lookup concrete_stack symbol with
            | Some value => Some value
            | None => match spec with 
                       | SFS _ _ sfsm => match lookup sfsm symbol with
                                        | Some (SFSconst v) => Some v
                                        | Some (SFSbinop oper name1 name2) => 
                                            match (evaluate_sfs_from_map d' concrete_stack spec name1,
                                                   evaluate_sfs_from_map d' concrete_stack spec name2) with
                                             | (Some v1, Some v2) => evaluate_concrete_element oper (v1::v2::nil)
                                             | _ => None
                                            end
                                        | Some (SFSname name) => evaluate_sfs_from_map d' concrete_stack spec name
                                        | None => None
                                       end
                      end
           end
end.


Lemma eval_more_steps: forall (d: nat) (stack: map EVMWord) (absi abso: abstract_stack) 
(sfs_map: sfs_map) (symbol: string) (val: EVMWord),
evaluate_sfs_from_map d stack (SFS absi abso sfs_map) symbol = Some val
-> evaluate_sfs_from_map (S d) stack (SFS absi abso sfs_map) symbol = Some val.
Proof.
intro d. induction d as [ | d' IH].
 - intros stack absi abso sfs_map symbol val.
   unfold evaluate_sfs_from_map. intro Hnonesome. discriminate.
 - intros stack absi abso sfs_map symbol val.
   remember (S d') as succdp eqn: Heqsuccdp. (* Defines succdp = S d', useful for unfolding *)
   rewrite -> Heqsuccdp at 1.
   unfold evaluate_sfs_from_map.
   destruct (lookup stack symbol) as [v | ] eqn: eqlookupstackvalue; try trivial.
   destruct (lookup sfs_map symbol) as [v | ] eqn: eqlookupmapvalue; try trivial.
   destruct v as [value|name|op name1 name2] eqn: Hv.
   + trivial.
   + fold evaluate_sfs_from_map.
     rewrite -> Heqsuccdp.
     pose proof (IH stack absi abso sfs_map name val) as IHspec.
     rewrite -> Heqsuccdp in IHspec.
     assumption.
   + fold evaluate_sfs_from_map.
     destruct (evaluate_sfs_from_map d' stack (SFS absi abso sfs_map) name1) 
       as [v1|] eqn: Hevalname1.
     * destruct (evaluate_sfs_from_map d' stack (SFS absi abso sfs_map) name2) 
          as [v2|] eqn: Hevalname2.
       -- pose proof (IH stack absi abso sfs_map name1 v1) as IHspecname1.
          apply IHspecname1 in Hevalname1.
          rewrite -> Hevalname1.
          pose proof (IH stack absi abso sfs_map name2 v2) as IHspecname2.
          apply IHspecname2 in Hevalname2.
          rewrite -> Hevalname2.
          trivial.
       -- intro Hfalse. discriminate.
     * intro Hfalse. discriminate.
Qed.



Fixpoint evaluate_sfs_aux (d: nat) (abs: abstract_stack) (stack: map EVMWord) (sfsm: sfs_map): 
                          option (list EVMWord) := 
match abs with
| nil => Some nil
| symb::r => match (evaluate_sfs_from_map d stack (SFS nil nil sfsm) symb,
                    evaluate_sfs_aux d r stack sfsm) with
             | (Some vs, Some rr) => Some (vs::rr)
             | _ => None
             end
end.

Definition evaluate_sfs (d: nat) (csfs: sfs) (stack: list EVMWord) : option (list EVMWord) := 
match csfs with
| SFS absi abso smap => let stack := combine absi stack in
                        evaluate_sfs_aux d abso stack smap
end.

Definition infinite_eval_steps : nat := 5000. (* This should be enough in SFS obtained in our blocks *)

Compute (let csfs := SFS ("s0"::"s1"::"s2"::"s3"::nil) ("e1"::"s3"::nil) 
                         (("e0", SFSbinop (SimplePriceOpcodeMk MUL) "s0" "s1")::
                         (("e1", SFSbinop (SimplePriceOpcodeMk ADD) "e0" "s2")::nil))
         in evaluate_sfs infinite_eval_steps csfs 
           ((natToWord WLen 2)::(natToWord WLen 3)::(natToWord WLen 5)::(natToWord WLen 7)::nil)).




(**********
 Generation of abstract stacks of a given size
 **********)

Definition nat_to_ascii_digit (n: nat) : string := 
  let num := modulo n 10 in
  string_of_list_ascii ((ascii_of_nat ((nat_of_ascii "0") + n))::nil).

(* 'depth' is the fake argument for strong normalization *)
Fixpoint nat_to_string_aux (n: nat) (depth:nat): string :=
match depth with
 | 0 => ""
 | S m => if n <? 10 then (nat_to_ascii_digit n) 
          else
            let last_digit := modulo n 10 in
            let rest_num := div n 10 in
            append (nat_to_string_aux rest_num m) (nat_to_ascii_digit last_digit)
end.

(* String of the last 50 digits in 'n' *)
Definition nat_to_string (n: nat) : string :=
nat_to_string_aux n 50.


Fixpoint create_abs_stack_name_rev (n: nat) (prefix: string): list string :=
match n with
 | 0 => nil
 | S m => ((append prefix (nat_to_string m))::(create_abs_stack_name_rev m prefix)) 
end.

(* Creates an abstract stack of 'n' symbols with the given prefix *)
Definition create_abs_stack_name (n: nat) (prefix: string): list string :=
rev (create_abs_stack_name_rev n prefix).

Compute (create_abs_stack_name 10 "s").





(*****************
 Abstract evaluation: generation of SFS from EVM bytecode
 Receive the size and use always sN for initial stack elements and eN for generated ones
*****************)

Definition prefix_abstract_stack : string := "s".
Definition prefix_abstract_stack_eval : string := "e".
 

(* arg is a word of length 5 that represents the argument of the PUSH: PUSH1 = PUSH 00000, PUSH2 = PUSH 00001, etc. *)
Definition abs_eval_push (arg: word 5) (word: EVMWord) (curr_sfs: sfs) (fresh_stack_id: nat)
  : option (sfs * nat) :=
match curr_sfs with
 | SFS absi abso sfs_map => let value := pushWordPass word (wordToNat arg + 1) in
                            let stack_pos_name := append prefix_abstract_stack_eval (nat_to_string fresh_stack_id) in
                            Some (SFS absi 
                                      (stack_pos_name::abso) 
                                      (update sfs_map stack_pos_name (SFSconst value)), 
                                 fresh_stack_id + 1)
end.


Definition abs_eval_pop (curr_sfs: sfs) (fresh_stack_id: nat)
  : option (sfs * nat) :=
match curr_sfs with
 | SFS absi abso sfs_map => match abso with
                             | top::r => Some ((SFS absi r sfs_map), fresh_stack_id)
                             | nil => None
                            end
end.

(* General code for every simple binary operation in the stack *)
Definition abs_eval_binary (oper: OpCode) (curr_sfs: sfs) (fresh_stack_id: nat)
  : option (sfs * nat) :=
match curr_sfs with
| SFS absi abso sfs_map => match abso with
                           | s0::s1::rstack => 
                               let stack_pos_name := append "e" (nat_to_string fresh_stack_id) in 
                               Some (SFS absi 
                                         (stack_pos_name::rstack) 
                                         (update sfs_map stack_pos_name (SFSbinop oper s0 s1)),
                                     fresh_stack_id + 1)
                           | _ => None
                           end
end.

Compute abs_eval_binary (SimplePriceOpcodeMk ADD) (SFS ("s0"::"s1"::nil) ("s0"::"s1"::nil) empty_map) 0.
Compute abs_eval_binary (SimplePriceOpcodeMk SUB) (SFS ("s0"::"s1"::"s2"::nil) ("s0"::"s1"::"s2"::nil) empty_map) 3.


(* Function to evaluate an operation in a SFS *)
Definition abs_eval_op (oper: OpCode) (curr_sfs: sfs) (fresh_stack_id: nat)
  : option (sfs * nat) :=
match oper with
  | SimplePriceOpcodeMk ADD => abs_eval_binary (SimplePriceOpcodeMk ADD) curr_sfs fresh_stack_id
  | SimplePriceOpcodeMk MUL => abs_eval_binary (SimplePriceOpcodeMk MUL) curr_sfs fresh_stack_id
  | SimplePriceOpcodeMk SUB => abs_eval_binary oper curr_sfs fresh_stack_id
  | SimplePriceOpcodeMk (PUSH arg word) => abs_eval_push arg word curr_sfs fresh_stack_id
  | SimplePriceOpcodeMk POP => abs_eval_pop curr_sfs fresh_stack_id
 (* All binary instructions are evaluated the same
  | DIV	          => 5
  | SDIV	        => 5
  | MOD	          => 5
  | SMOD	        => 5
  | ADDMOD	      => 8
  | MULMOD	      => 8
  ----
  *)
  | _ => None
end.

Check (abs_eval_op).
Compute abs_eval_op (SimplePriceOpcodeMk ADD) (SFS ("s0"::"s1"::nil) ("s0"::"s1"::nil) empty_map) 5.
Compute abs_eval_op (SimplePriceOpcodeMk SUB) (SFS ("s0"::"s1"::nil) ("s0"::"s1"::nil) empty_map) 0.


Fixpoint abstract_eval_aux (program: list OpCode) (curr_sfs: sfs) (fresh_stack_id: nat)
  : option (sfs * nat) :=
match program with 
  | nil => Some (curr_sfs, fresh_stack_id)
  | oper::rprog => match abs_eval_op oper curr_sfs fresh_stack_id with
                    | None => None
                    | Some (new_sfs, new_fresh_stack_id) => abstract_eval_aux rprog new_sfs new_fresh_stack_id
                   end
end.

Definition abstract_eval (stack_size: nat) (program: list OpCode)
  : option sfs :=
let ins := create_abs_stack_name stack_size prefix_abstract_stack in
match abstract_eval_aux program (SFS ins ins empty_map) 0 with (* fresh stack positions starting from 0 *)
 | None => None
 | Some (final_sfs, _) => Some final_sfs
end.


Check abstract_eval 3 (SimplePriceOpcodeMk ADD::nil).
Compute (abstract_eval 3 (SimplePriceOpcodeMk ADD::nil)).
Compute (abstract_eval 5 (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk MUL::nil)).
Compute (abstract_eval 2 (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk POP::nil)).
Compute (abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 10))::SimplePriceOpcodeMk POP::nil)).



Example push_4_3:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 4))::
                       SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 3))::
                       SimplePriceOpcodeMk ADD::
                       nil) with
 | Some csfs => (*Some csfs*)
                (evaluate_sfs_from_map 1024 empty_map csfs "e0",
                 evaluate_sfs_from_map 1024 empty_map csfs "e1",
                 evaluate_sfs_from_map 1024 empty_map csfs "e2",
                 evaluate_sfs_from_map 1024 empty_map csfs "s0",
                 evaluate_sfs_from_map 1024 empty_map csfs "e3")
 | _ => (None, None, None, None, None)
end = (Some (natToWord WLen 4), 
       Some (natToWord WLen 3),
       Some (natToWord WLen 7),
       None,
       None).
Proof.
 reflexivity. Qed.



Definition safeWordToNat (w: option EVMWord) : option nat :=
match w with
 | None => None
 | Some w => Some (wordToNat w)
end.


Example map_s1:
         (let init_map := ("s0", natToWord WLen 6)::("s1", (natToWord WLen 5))::nil in 
         let spec := SFS nil nil (("e0", SFSbinop (SimplePriceOpcodeMk ADD) "s0" "s1")::nil) in 
         safeWordToNat (evaluate_sfs_from_map StackLen init_map spec "s1")) = Some 5.
Proof. reflexivity. Qed.

Example map_e0:
         (let init_map := ("s0", natToWord WLen 6)::("s1", (natToWord WLen 5))::nil in 
         let spec := SFS nil nil (("e0", SFSbinop (SimplePriceOpcodeMk ADD) "s0" "s1")::nil) in 
         safeWordToNat (evaluate_sfs_from_map StackLen init_map spec "e0")) = Some 11.
Proof. reflexivity. Qed.

Example map_e1:
         (let init_map := ("s0", natToWord WLen 6)::("s1", (natToWord WLen 5))::("s2", (natToWord WLen 2))::nil in 
         let spec := SFS nil nil (("e0", SFSbinop (SimplePriceOpcodeMk ADD) "s0" "s1")::
                              ("e1", SFSbinop (SimplePriceOpcodeMk MUL) "e0" "s2")::nil) in 
         safeWordToNat (evaluate_sfs_from_map StackLen init_map spec "e1")) = Some 22.
Proof. reflexivity. Qed.

Example map_e2:
         (let init_map := ("s0", natToWord WLen 6)::("s1", (natToWord WLen 5))::
                         ("s2", (natToWord WLen 2))::("s3", (natToWord WLen 2))::nil in 
         let spec := SFS nil nil (("e0", SFSbinop (SimplePriceOpcodeMk ADD) ("s0") ("s1"))::
                              ("e1", SFSbinop (SimplePriceOpcodeMk MUL) ("e0") ("s2"))::
                              ("e2", SFSbinop (SimplePriceOpcodeMk SUB) ("e1") ("s3"))::nil) in 
         safeWordToNat (evaluate_sfs_from_map StackLen init_map spec "e2")) = Some 20.
Proof. reflexivity. Qed.


(* Combining the abstract evaluation of a program and the concrete evaluation of a final stack position *)
Example ex1: 
let program := (SimplePriceOpcodeMk ADD::SimplePriceOpcodeMk MUL::nil) in
let stack   := (natToWord WLen 2)::(natToWord WLen 5)::(natToWord WLen 3)::(natToWord WLen 6)::nil in
let sfso := abstract_eval 3 program in
let stack_map := combine (create_abs_stack_name 4 "s") stack in
match sfso with
 | None => None
 | Some sfs => match (safeWordToNat (evaluate_sfs_from_map StackLen stack_map sfs "e1")) with
                | None => None
                | Some v => Some v
               end
end = Some 21.
Proof. reflexivity. Qed.

(* Two SFS specifications are the same if given a concrete stack, they evaluate their final abstract
   stacks to the same EVM values (EVMWord)
   I need to split the 3 arguments of SFS so that Coq detects the decreasing one
*)
Fixpoint sfs_equiv_concrete_values_aux (stack_map1 stack_map2: map EVMWord) 
  (absi1 absi2 abso1 abso2: abstract_stack) (sfsmap1 sfsmap2: sfs_map) : bool :=
match (abso1, abso2) with
  | (nil, nil) => true  
  | (symb1::r1, symb2::r2) => 
      let v1 := evaluate_sfs_from_map 1024 stack_map1 (SFS absi1 abso1 sfsmap1) symb1 in
      let v2 := evaluate_sfs_from_map 1024 stack_map2 (SFS absi2 abso2 sfsmap2) symb2 in
      match (v1, v2) with
       | (Some w1, Some w2) => (weqb w1 w2) && 
                               (sfs_equiv_concrete_values_aux stack_map1 stack_map2 absi1 absi2 r1 r2 sfsmap1 sfsmap2)
       | _ => false
      end
  | _ => false
end.

Locate eqb.

(* Two SFS are equivalent for a concrete stack if both have the same length and each SFS maps every
   stack position to the same concrete value (wrt. the concrete stack) *)
Definition sfs_equiv_concrete_values (concrete_stack: list EVMWord) (spec1 spec2: sfs) : bool :=
match (spec1, spec2) with
 | (SFS absi1 abso1 sfsmap1, SFS absi2 abso2 sfsmap2) => 
      let stack_map1 := combine absi1 concrete_stack in
      let stack_map2 := combine absi2 concrete_stack in
      andb (Nat.eqb (List.length concrete_stack) (List.length absi1))
           (andb ((Nat.eqb (List.length concrete_stack) (List.length absi2)) )
           (sfs_equiv_concrete_values_aux stack_map1 stack_map2 absi1 absi2 abso1 abso2 sfsmap1 sfsmap2))
end.
Check sfs_equiv_concrete_values.


(* Generates an empty list of the same EVMWord *)
Fixpoint empty_concrete_stack (n: nat) : list EVMWord :=
match n with
 | 0 => nil
 | S n' => WZero :: (empty_concrete_stack n')
end.

(* Generates a full stack (mapping) from s_n to WZero *)
Definition full_empty_stack_map : map EVMWord :=
 let len := StackLen in
 List.combine (create_abs_stack_name len prefix_abstract_stack) (empty_concrete_stack len).
 

(* TODO: fix definitions, this should return Some true*)
Example push_add:
let init_stack := empty_concrete_stack 0 in
let osfs1 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 15)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 0)))::
                           SimplePriceOpcodeMk ADD::
                           nil) in
let osfs2 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 15)))::
                           nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some true.
Proof. reflexivity. Qed.

Example stack_0: create_abs_stack_name 0 prefix_abstract_stack = nil.
Proof. reflexivity. Qed.


Example push_equiv:
let init_stack := nil in
let osfs1 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 10)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 5)))::
                           SimplePriceOpcodeMk ADD::
                           nil) in
let osfs2 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 5)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 5)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 5)))::
                           SimplePriceOpcodeMk ADD::
                           SimplePriceOpcodeMk ADD::
                           nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some true.
Proof. reflexivity. Qed.

Example push_equiv2:
let init_stack := nil in
let osfs1 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 10)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 5)))::
                           SimplePriceOpcodeMk ADD::
                           nil) in
let osfs2 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 15)))::
                           nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some true.
Proof. reflexivity. Qed.

Example push_equiv_false:
let init_stack := nil in
let osfs1 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 10)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 4)))::
                           SimplePriceOpcodeMk ADD::
                           nil) in
let osfs2 := abstract_eval 0 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 15)))::
                           nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some false.
Proof. reflexivity. Qed.


Compute (abstract_eval 2 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 2)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 8)))::
                           SimplePriceOpcodeMk MUL::
                           nil)).
Compute (abstract_eval 2 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 16)))::
                           nil)).


Compute (List.length (natToWord WLen 7 :: natToWord WLen 19 :: nil)). 
Compute ((Datatypes.length (create_abs_stack_name 2 prefix_abstract_stack))).


Example push_equiv3:
let init_stack := (natToWord WLen 7)::(natToWord WLen 19)::nil in
let osfs1 := abstract_eval 2 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 2)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 8)))::
                           SimplePriceOpcodeMk MUL::
                           nil) in
let osfs2 := abstract_eval 2 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 16)))::
                           nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some true.
Proof. reflexivity. 
Qed.

Example push_equiv_false2:
let init_stack := (natToWord WLen 7)::(natToWord WLen 19)::nil in
let osfs1 := abstract_eval 2 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 2)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 8)))::
                           SimplePriceOpcodeMk MUL::
                           nil) in
let osfs2 := abstract_eval 2 ((SimplePriceOpcodeMk POP)::(SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 16)))::
                           nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some false.
Proof. reflexivity. Qed.

Example push_equiv4:
let init_stack := (natToWord WLen 7)::(natToWord WLen 19)::nil in
let osfs1 := abstract_eval 2 ((SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 3)))::
                           (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 4)))::
                           SimplePriceOpcodeMk MUL::
                           nil) in
let osfs2 := abstract_eval 2 ((SimplePriceOpcodeMk POP)::
                              (SimplePriceOpcodeMk POP)::
                              (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 19)))::
                              (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 7)))::
                              (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 12)))::
                              nil) in
match (osfs1, osfs2) with
 | (Some sfs1, Some sfs2) => Some (sfs_equiv_concrete_values init_stack sfs1 sfs2)
 | _ => None
end = Some true.
Proof. reflexivity. Qed. 



