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
Require Import Coq_EVM.sfs.



(*************
  POINTS-TO symbol to constant in SFS map
 *************)

(* Checks if the mapping of the 'label' in the 'smap' is the constant 'value' in one step *)
Definition points_to_const (label: string) (smap: sfs_map) (value: EVMWord) : bool :=
match lookup smap label with
 | Some (SFSconst val) => weqb val value
 | _ => false
end.


Example pointso_ex1: 
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WZero)::
                     SimplePriceOpcodeMk ADD::
                     nil) with
 | Some (SFS absi abso sfsmap) => Some (points_to_const "e0" sfsmap WZero)
 | _ => None
end = Some true.
Proof. reflexivity. Qed.

Example pointso_ex2:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 55 ))::
                     SimplePriceOpcodeMk ADD::
                     nil) with
 | Some (SFS absi abso sfsmap) => Some (points_to_const "e0" sfsmap WZero)
 | _ => None
end = Some false.
Proof. reflexivity. Qed.

Example pointso_ex3:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 55 ))::
                     SimplePriceOpcodeMk ADD::
                     nil) with
 | Some (SFS absi abso sfsmap) => Some (points_to_const "e1" sfsmap WZero)
 | _ => None
end = Some false.
Proof. reflexivity. Qed.


Lemma points_to_then_eval: forall (d:nat) (symb: string) (absi abso: abstract_stack)
      (sfs_map: sfs_map) (value val: EVMWord) (concrete_stack: map EVMWord),
 (points_to_const symb sfs_map value) = true
 -> lookup concrete_stack symb = None
 -> evaluate_sfs_from_map d concrete_stack (SFS absi abso sfs_map) symb = Some val 
 -> val = value.
Proof. 
 intros d symb absi abso csfs_map value val concrete_stack.
 unfold points_to_const.
 destruct (lookup csfs_map symb) as [s|] eqn: eqlookup.
 + destruct s as [ | name | ] eqn: eqs.
   - unfold evaluate_sfs_from_map. destruct d as [ | d'] eqn: eqd.
     * intros Heq HNonesome. discriminate.
     * intros Heq Hlookup. rewrite -> Hlookup.
       rewrite -> eqlookup.
       destruct d' as [ | d''] eqn: eqd'.
       ++ intros Hvval. injection Hvval.
          injection Hvval.
          intro eqvval.
          apply weqb_true_iff in Heq.
          rewrite -> Heq. intros Hvalueval.
          symmetry. assumption.
       ++ intros Hvval. injection Hvval.
          injection Hvval.
          intro eqvval.
          apply weqb_true_iff in Heq.
          rewrite -> Heq. intros Hvalueval.
          symmetry. assumption.
  - destruct (lookup csfs_map name) eqn: eqlookup2.
    * intros falsetrue. discriminate.
    * intros falsetrue. discriminate.
  - intros falsetrue. discriminate.
 + intros falsetrue. discriminate.
Qed.


(* If points_to detect that a symbol points to a constant in the SFS, then it cannot 
   appear in the stack because they are disjoint *)
Lemma points_to_not_in_stack: forall (stack: map EVMWord) (absi abso: abstract_stack) 
                             (sfs_map: sfs_map) (name: string) (val: EVMWord),
disjoint_stack_sfs stack (SFS absi abso sfs_map)
-> points_to_const name sfs_map val = true
-> lookup stack name = None.
Proof.
intros stack absi abso ini_sfs_map name val.
unfold disjoint_stack_sfs.
intro Hdisjoint.
unfold points_to_const.
destruct (lookup ini_sfs_map name) as [valname|] eqn: Hlookupmap;
  try (intro Hfalse; discriminate).
destruct valname as [constname|rname|op name1 name2] eqn: Hvalname;
  try (intro Hfalse; discriminate).
pose proof (@lookup_then_key_in_domain sfs_val ini_sfs_map name
  (SFSconst constname) Hlookupmap) as Hname_in_sfsmap.
pose proof (disjoint_then_not_in (domain stack) (domain ini_sfs_map)
  name Hdisjoint).
pose proof (disjoint_sym (domain stack) (domain ini_sfs_map) Hdisjoint)
  as Hdisjoint_sym.
pose proof (disjoint_then_not_in (domain ini_sfs_map) (domain stack)
  name Hdisjoint_sym Hname_in_sfsmap) as Hname_not_in_stack.
intro Heqconst.
pose proof (@not_in_domain_then_lookup_none EVMWord stack name
  Hname_not_in_stack) as Hlookup_none.
assumption.
Qed.



(**************
  OPTIMIZATION X+0 -> X
 **************)

(* ADD(X, 0) -> X and ADD(0, X) -> X *)
Definition optimize_add_zero (var: string) (s: sfs) : option sfs :=
match s with
 | SFS absi abso smap => 
     match lookup smap var with
      | Some (SFSbinop (SimplePriceOpcodeMk ADD) a b) =>
          if points_to_const a smap WZero then Some (SFS absi abso (update smap var (SFSname b)))
          else if points_to_const b smap WZero then Some (SFS absi abso (update smap var (SFSname a)))
          else None
      | _ => None
     end
end.

Example opt_addzero1:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WZero)::
                               SimplePriceOpcodeMk ADD::
                               nil) with
| Some sfsini => match optimize_add_zero "e1" sfsini with
                 | Some sfs => Some sfs
                 | None => None
                 end
| None => None
end = 
Some (SFS ("s0"::nil) ("e1"::nil) 
          (("e1", SFSname "s0"):: (* updated mapping from optimize_add_zero *)
           ("e1", SFSbinop (SimplePriceOpcodeMk ADD) "e0" "s0"):: (* old one *)
           ("e0", SFSconst WZero)::nil)).
Proof. reflexivity. Qed.

Example opt_addzero2: 
match abstract_eval 0 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WZero)::
                     SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 15))::
                     SimplePriceOpcodeMk ADD::
                     nil) with
 | Some (SFS absi abso smap) => optimize_add_zero "e2" (SFS absi abso smap)
 | _ => None
end = 
Some (SFS nil ("e2"::nil)
          (("e2", SFSname "e1"):: (* updated mapping from optimize_add_zero *)
           ("e2", SFSbinop (SimplePriceOpcodeMk ADD) "e1" "e0"):: (* old one *)
           ("e1", SFSconst (natToWord WLen 15))::
           ("e0", SFSconst WZero)::nil)).
Proof. reflexivity. Qed.

Example opt_addzero3: 
match abstract_eval 0 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WZero)::
                     SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 15))::
                     SimplePriceOpcodeMk ADD::
                     nil) with
 | Some (SFS absi abso smap) => optimize_add_zero "e1" (SFS absi abso smap)
 | _ => None
end = None. (* e1 points to 15 *)
Proof. reflexivity. Qed.


Lemma optimize_add_zero_same_abs: forall (symb: string)
      (absi abso opt_absi opt_abso: abstract_stack) (ini_sfs_map opt_sfs_map: sfs_map), 
optimize_add_zero symb (SFS absi abso ini_sfs_map) = Some (SFS opt_absi opt_abso opt_sfs_map) ->
absi = opt_absi /\ abso = opt_abso.
Proof.
intros symb absi abso opt_absi opt_abso ini_sfs_map opt_sfs_map.
unfold optimize_add_zero.
destruct (lookup ini_sfs_map symb) as [sfsvalue|] eqn:eqlookupsymb; try discriminate.
destruct sfsvalue as [ | |op name1 name2] eqn: eqsfsvalue; try discriminate.
destruct op as [ | | |instr] eqn: eqop; try discriminate.
 (* Tries to apply discrimiante for all instructions 'op', that succeeds except 
    for SimplePriceOpcodeMk *)
destruct instr eqn: eqinstr; try discriminate. 
(* Tries to apply discrimiante for all simple instructions 'instr', that succeeds except 
   for ADD *)
destruct (points_to_const name1 ini_sfs_map WZero) eqn: eqhaszeroa.
 - intro Hini_opt. injection Hini_opt. intros Hopt_map Hopt_abs Hopt_absi. 
   split; try assumption.
 - destruct (points_to_const name2 ini_sfs_map WZero) eqn: eqhaszerob; try discriminate.
   intro Hini_opt. injection Hini_opt. intros Hopt_map Hopt_abs hOpt_absi.
   split; try assumption.
Qed.



Lemma optimize_add_zero_symb_same_value_init: 
 forall (d: nat) (concrete_stack: map EVMWord) (ini_sfs opt_sfs: sfs) (symb: string)
 (c: EVMWord),
 lookup concrete_stack symb = Some c
 -> optimize_add_zero symb ini_sfs = Some opt_sfs
 -> evaluate_sfs_from_map d concrete_stack ini_sfs symb =
    evaluate_sfs_from_map d concrete_stack opt_sfs symb.
Proof.
 intros d stack ini_sfs opt_sfs symb c Hlookup HoptSome.
 unfold evaluate_sfs_from_map.
 unfold evaluate_sfs_from_map. destruct d as [ | d'] eqn:eqd; try reflexivity.
 rewrite -> Hlookup. reflexivity.
Qed.


(* Evaluating X+0 = X in EVM words *)
Lemma evalADDzero: forall (e: EVMWord),
 evaluate_concrete_element (SimplePriceOpcodeMk ADD) (WZero :: e :: nil) = Some e.
Proof.
 intros e. unfold evaluate_concrete_element. simpl.
 unfold WZero.
 rewrite -> wplus_wzero_2.
 reflexivity.
 Qed.
 
(* Evaluating 0+X = X in EVM words *) 
Lemma evalADDzero2: forall (e: EVMWord),
 evaluate_concrete_element (SimplePriceOpcodeMk ADD) (e :: WZero :: nil) = Some e.
Proof.
 intros e. unfold evaluate_concrete_element. simpl.
 unfold WZero.
 rewrite -> wplus_wzero_1.
 reflexivity.
 Qed.


(* If you can apply  the X+0 optimization in symbol 'symb', then it must be mapped
   to a some addition name1 + name2 in the SFS *)
Lemma opt_add_zero_then_binopADD: forall (absi abso opt_absi opt_abso: abstract_stack) 
   (ini_sfs_map opt_sfs_map: sfs_map) (symb: string),
optimize_add_zero symb (SFS absi abso ini_sfs_map) = Some (SFS opt_absi opt_abso opt_sfs_map) ->
exists (name1 name2: string), lookup ini_sfs_map symb = Some (SFSbinop 
  (SimplePriceOpcodeMk ADD) name1 name2).
Proof.
intros absi abso opt_absi opt_abso ini_sfs_map opt_sfs_map symb.
unfold optimize_add_zero.
destruct (lookup ini_sfs_map symb) as [symb_expr|] eqn: Hlookupsymb;
  try (intro Hfalse; discriminate).
destruct symb_expr as [value|name|op n1 n2]; try (intro Hfalse; discriminate).
destruct op as [ | | | oper]; try (intro Hfalse; discriminate).
destruct oper; try (intro Hfalse; discriminate).
destruct (points_to_const n1 ini_sfs_map WZero) eqn: Hpointsto_n1.
- intro Hopt. exists n1. exists n2. reflexivity.
- destruct (points_to_const n2 ini_sfs_map WZero) eqn: Hpointsto_name2; 
    try (intro Hfalse; discriminate).
  intro Hopt. exists n1. exists n2. reflexivity.
Qed.  


(* If you can apply the X+0 optimization in symbol 'symb', then the new SFS mapping
   is just the original one but replacing 'symb' *)
Lemma opt_add_zero_only_affects_symbol: forall (absi abso opt_absi opt_abso: abstract_stack) 
   (ini_sfs_map opt_sfs_map: sfs_map) (symb: string),
optimize_add_zero symb (SFS absi abso ini_sfs_map) = Some (SFS opt_absi opt_abso opt_sfs_map) ->
exists (sfsexpr: sfs_val), opt_sfs_map = update ini_sfs_map symb sfsexpr.
Proof.
intros absi abso opt_absi opt_abso ini_sfs_map opt_sfs_map symb.
unfold optimize_add_zero.
destruct (lookup ini_sfs_map symb) as [symb_expr|] eqn: Hlookupsymb;
  try (intro Hfalse; discriminate).
destruct symb_expr as [value|name|op n1 n2]; try (intro Hfalse; discriminate).
destruct op as [ | | | oper]; try (intro Hfalse; discriminate).
destruct oper; try (intro Hfalse; discriminate).
destruct (points_to_const n1 ini_sfs_map WZero) eqn: Hpointsto_n1.
- intro Hopt. injection Hopt. intro Hopt_sfs_map. intro Hopt_abs. 
  rewrite <- Hopt_sfs_map. exists (SFSname n2). reflexivity.
- destruct (points_to_const n2 ini_sfs_map WZero) eqn: Hpointsto_name2; 
    try (intro Hfalse; discriminate).
  intro Hopt. injection Hopt. intro Hopt_sfs_map. intro Hopt_abs. 
  rewrite <- Hopt_sfs_map. exists (SFSname n1). reflexivity.
Qed.


(* If you can apply the X+0 optimization in symbol 'symb', then the SFS mapping
   contained a name1 + name2 where
   a) name1 points to WZero and [symb |-> name2] in the new SFS mapping
   b) name1 does not point to WZero, name2 points to WZero and [symb |-> name1] 
        in the new SFS mapping *)
Lemma opt_add_zero_then_pointsto: forall (absi abso opt_absi opt_abso: abstract_stack) 
      (ini_sfs_map opt_sfs_map: sfs_map)
      (symb name1 name2: string),
optimize_add_zero symb (SFS absi abso ini_sfs_map) = Some (SFS opt_absi opt_abso opt_sfs_map) ->
lookup ini_sfs_map symb = 
  Some (SFSbinop (SimplePriceOpcodeMk ADD) name1 name2) ->
(points_to_const name1 ini_sfs_map WZero = true /\
 opt_sfs_map = update ini_sfs_map symb (SFSname name2)) 
\/ 
(points_to_const name1 ini_sfs_map WZero = false /\
 points_to_const name2 ini_sfs_map WZero = true /\
 opt_sfs_map = update ini_sfs_map symb (SFSname name1)).
Proof.
intros absi abso opt_absi opt_abso ini_sfs_map opt_sfs_map symb name1 name2.
unfold optimize_add_zero.
destruct (lookup ini_sfs_map symb) as [symb_expr|] eqn: Hlookupsymb;
  try (intro Hfalse; discriminate).
destruct symb_expr as [value|name|op n1 n2]; try (intro Hfalse; discriminate).
destruct op as [ | | | oper]; try (intro Hfalse; discriminate).
destruct oper; try (intro Hfalse; discriminate).
destruct (points_to_const n1 ini_sfs_map WZero) eqn: Hpointsto_n1.
- intro Hopt_sfs. injection Hopt_sfs. intros Hopt_sfs_map Hopt_absi Hopt_abso.
  intro Hsfsexpr. injection Hsfsexpr. intros Hn2 Hn1.
  left.
  symmetry in Hopt_sfs_map.
  rewrite <- Hn1.
  rewrite <- Hn2.
  split; try assumption.
- destruct (points_to_const n2 ini_sfs_map WZero) eqn: Hpointsto_n2; 
    try (intro Hfalse; discriminate).
  intro Hopt_sfs. injection Hopt_sfs. intros Hopt_sfs_map Hopt_absi Hopt_abso.
  intro Hsfsexpr. injection Hsfsexpr. intros Hn2 Hn1.
  right.
  symmetry in Hopt_sfs_map.
  rewrite <- Hn1.
  rewrite <- Hn2.
  split; try assumption.
  split; try assumption.
Qed.


(* In the add-zero optimization of symbol 'symb', all the other symbols points to the 
   SFS expression *)
Lemma optimize_add_zero_same_but_symb: 
 forall (symb symb2: string)
 (absi abso opt_absi opt_abso: abstract_stack) (ini_sfs_map opt_sfs_map: sfs_map), 
 symb =? symb2 = false
 -> optimize_add_zero symb (SFS absi abso ini_sfs_map) = Some (SFS opt_absi opt_abso opt_sfs_map) 
 -> lookup ini_sfs_map symb2 = lookup opt_sfs_map symb2.
Proof.
 intros symb symb2 absi abso opt_absi opt_abso ini_sfs_map opt_sfs_map HSymb Hopt.
 pose proof (opt_add_zero_only_affects_symbol absi abso opt_absi opt_abso ini_sfs_map
    opt_sfs_map symb Hopt) as Haffect_ex.
 destruct Haffect_ex as [sfsval Haffect].
 rewrite -> Haffect.
 pose proof (update_lookup_diff sfs_val ini_sfs_map symb symb2 sfsval
   HSymb) as Hlookup.
 rewrite -> Hlookup.
 reflexivity.
Qed.



Lemma pointsto_and_none_then_0_steps: forall (d: nat) (absi abso: abstract_stack)
  (ini_sfs_map: sfs_map) (stack: map EVMWord) (val: EVMWord) (symbol: string),
disjoint_stack_sfs stack (SFS absi abso ini_sfs_map) ->
points_to_const symbol ini_sfs_map val = true ->
evaluate_sfs_from_map d stack (SFS absi abso ini_sfs_map) symbol = None ->
d = 0.
Proof.
intros d absi abso ini_sfs_map stack val symbol Hdisjoint Hpointsto Heval.
(*remember Hpointsto as Hpointsto_orig eqn: eqpointsto. *)
(*unfold points_to_const in Hpointsto.*)
destruct (lookup ini_sfs_map symbol) as [sfs_expr|] eqn: eqlookup.
- destruct (sfs_expr) as [const|name|name1 name2] eqn: eqsfs_expr.
  * (* SFSconst *)
    unfold evaluate_sfs_from_map in Heval.
    destruct d as [|d']; try reflexivity.
    pose proof (points_to_not_in_stack stack absi abso ini_sfs_map symbol val
      Hdisjoint Hpointsto) as Hnotinstack.
    rewrite -> Hnotinstack in Heval.
    rewrite -> eqlookup in Heval.
    discriminate.
  * (* SFSname *)
    unfold points_to_const in Hpointsto.
    rewrite -> eqlookup in Hpointsto.
    discriminate.
  * (* SFSbinop oper name1 name2 *) 
    unfold points_to_const in Hpointsto.
    rewrite -> eqlookup in Hpointsto.
    discriminate.
- unfold points_to_const in Hpointsto.
  rewrite -> eqlookup in Hpointsto.
  discriminate.
Qed.



(* 
   MAIN THEOREM FOR THE X+0 OPTIMIZATION 
   Evaluating a symbol in the original SFS returns the same as evaluating
   it in the optimized SFS 
*)
Theorem optimize_add_zero_correct: forall (d: nat) 
        (concrete_stack: map EVMWord) (ini_sfs opt_sfs: sfs) 
        (symbol_opt symbol: string),
disjoint_stack_sfs concrete_stack ini_sfs ->
optimize_add_zero symbol_opt ini_sfs = Some opt_sfs ->
evaluate_sfs_from_map d concrete_stack ini_sfs symbol = 
evaluate_sfs_from_map d concrete_stack opt_sfs symbol.
Proof.
intro d. induction d as [|d' IH].
- intros stack ini_sfs opt_sfs symbol_opt symbol Hdisjoint Hopt.
  reflexivity.
- intros stack ini_sfs opt_sfs symbol_opt symbol Hdisjoint Hopt.
  destruct ini_sfs as [absi abso ini_sfs_map] eqn: eqini_sfs.
  destruct opt_sfs as [opt_absi opt_abso opt_sfs_map] eqn: eqopt_sfs.
  unfold evaluate_sfs_from_map.
  destruct (lookup stack symbol) as [valstack|] eqn: eqlookupstack; try trivial.
  (* lookup stack symbol = None *)
  destruct (symbol_opt =? symbol) eqn: eqsymbolopt.
  + (* Evaluating the same symbol that was optimized *)
    pose proof (opt_add_zero_then_binopADD absi abso opt_absi opt_abso ini_sfs_map
       opt_sfs_map symbol_opt Hopt) as Hlookup_opt_symb_exists.
    destruct Hlookup_opt_symb_exists as [name1 Hlookup_opt_symb_exists2].
    destruct Hlookup_opt_symb_exists2 as [name2 Hlookup_opt_symb].
    apply -> eqb_eq in eqsymbolopt.
    rewrite -> eqsymbolopt in Hlookup_opt_symb.
    rewrite -> Hlookup_opt_symb.
    fold evaluate_sfs_from_map.
    rewrite -> eqsymbolopt in Hopt.
    pose proof (opt_add_zero_then_pointsto absi abso opt_absi opt_abso ini_sfs_map 
       opt_sfs_map symbol name1 name2 Hopt Hlookup_opt_symb) as Hoptimize_cases.
    destruct Hoptimize_cases as [Hoptimize_name1 | Hoptimize_name2].
    * destruct Hoptimize_name1 as [Hpointsto_name1 Hlookup_opt_symbol].
      destruct (evaluate_sfs_from_map d' stack (SFS absi abso ini_sfs_map) name1)
         as [val1 | ] eqn: eqevalname1.
      -- destruct (evaluate_sfs_from_map d' stack (SFS absi abso ini_sfs_map) name2)
            as [val2 |] eqn: eqevalname2.
         ++ pose proof (points_to_not_in_stack stack absi abso ini_sfs_map name1
               WZero Hdisjoint Hpointsto_name1) as Hname1_not_in_stack.
            pose proof (points_to_then_eval d' name1 absi abso ini_sfs_map WZero 
               val1 stack Hpointsto_name1 Hname1_not_in_stack eqevalname1) as Hval1_zero.
            rewrite -> Hval1_zero.
            rewrite -> evalADDzero.
            rewrite -> Hlookup_opt_symbol.
            pose proof (update_lookup sfs_val ini_sfs_map symbol 
               (SFSname name2)) as Hlookup_symbol_opt.
            rewrite -> Hlookup_symbol_opt.
            rewrite <- Hlookup_opt_symbol.
            rewrite <- eqopt_sfs.
            rewrite <- eqini_sfs in Hdisjoint.
            rewrite <- eqini_sfs in Hopt.
            rewrite <- eqopt_sfs in Hopt.
            rewrite <- eqini_sfs in eqevalname2.
            pose proof (IH stack ini_sfs opt_sfs symbol name2
               Hdisjoint Hopt) as IHspec.
            rewrite <- IHspec.
            rewrite -> eqevalname2.
            reflexivity.
         ++ pose proof (points_to_not_in_stack stack absi abso ini_sfs_map name1
               WZero Hdisjoint Hpointsto_name1) as Hname1_not_in_stack.
            pose proof (points_to_then_eval d' name1 absi abso ini_sfs_map WZero 
               val1 stack Hpointsto_name1 Hname1_not_in_stack eqevalname1) as Hval1_zero.
            rewrite -> Hlookup_opt_symbol.
            pose proof (update_lookup sfs_val ini_sfs_map symbol 
               (SFSname name2)) as Hlookup_symbol_opt.
            rewrite -> Hlookup_symbol_opt.
            rewrite <- Hlookup_opt_symbol.
            rewrite <- eqopt_sfs.
            rewrite <- eqini_sfs in Hdisjoint.
            rewrite <- eqini_sfs in Hopt.
            rewrite <- eqopt_sfs in Hopt.
            rewrite <- eqini_sfs in eqevalname2.
            pose proof (IH stack ini_sfs opt_sfs symbol name2
               Hdisjoint Hopt) as IHspec.
            rewrite <- IHspec.
            rewrite -> eqevalname2.
            reflexivity.
      -- rewrite -> Hlookup_opt_symbol.
         pose proof (pointsto_and_none_then_0_steps d' absi abso ini_sfs_map stack
           WZero name1 Hdisjoint Hpointsto_name1 eqevalname1) as Hdiszero.
         pose proof (update_lookup sfs_val ini_sfs_map symbol 
               (SFSname name2)) as Hlookup_symbol_opt.
         rewrite -> Hlookup_symbol_opt.
         rewrite -> Hdiszero.
         reflexivity.
    * destruct Hoptimize_name2 as [Hpointsto_name1 [Hpointsto_name2 Hlookup_opt_symbol]].
      destruct (evaluate_sfs_from_map d' stack (SFS absi abso ini_sfs_map) name1)
         as [val1 | ] eqn: eqevalname1.
      -- destruct (evaluate_sfs_from_map d' stack (SFS absi abso ini_sfs_map) name2)
            as [val2 |] eqn: eqevalname2.
         ++ pose proof (points_to_not_in_stack stack absi abso ini_sfs_map name2
               WZero Hdisjoint Hpointsto_name2) as Hname2_not_in_stack.
            pose proof (points_to_then_eval d' name2 absi abso ini_sfs_map WZero 
               val2 stack Hpointsto_name2 Hname2_not_in_stack eqevalname2) as Hval2_zero.
            rewrite -> Hval2_zero.
            rewrite -> evalADDzero2.
            rewrite -> Hlookup_opt_symbol.
            pose proof (update_lookup sfs_val ini_sfs_map symbol 
               (SFSname name1)) as Hlookup_symbol_opt.
            rewrite -> Hlookup_symbol_opt.
            rewrite <- Hlookup_opt_symbol.
            rewrite <- eqopt_sfs.
            rewrite <- eqini_sfs in Hdisjoint.
            rewrite <- eqini_sfs in Hopt.
            rewrite <- eqopt_sfs in Hopt.
            rewrite <- eqini_sfs in eqevalname1.
            pose proof (IH stack ini_sfs opt_sfs symbol name1
               Hdisjoint Hopt) as IHspec.
            rewrite <- IHspec.
            rewrite -> eqevalname1.
            reflexivity.
         ++ rewrite -> Hlookup_opt_symbol.
            pose proof (pointsto_and_none_then_0_steps d' absi abso ini_sfs_map stack
              WZero name2 Hdisjoint Hpointsto_name2 eqevalname2) as Hdiszero.
            pose proof (update_lookup sfs_val ini_sfs_map symbol 
               (SFSname name1)) as Hlookup_symbol_opt.
            rewrite -> Hlookup_symbol_opt.
            rewrite -> Hdiszero.
            reflexivity.
      -- rewrite -> Hlookup_opt_symbol.
         pose proof (update_lookup sfs_val ini_sfs_map symbol 
               (SFSname name1)) as Hlookup_symbol_opt.
         rewrite -> Hlookup_symbol_opt.
         rewrite <- Hlookup_opt_symbol.
         rewrite <- eqopt_sfs.
         rewrite <- eqini_sfs in Hdisjoint.
         rewrite <- eqini_sfs in Hopt.
         rewrite <- eqopt_sfs in Hopt.
         rewrite <- eqini_sfs in eqevalname1.
         pose proof (IH stack ini_sfs opt_sfs symbol name1
               Hdisjoint Hopt) as IHspec.
         rewrite <- IHspec.
         rewrite -> eqevalname1.
         reflexivity.
  + (* Evaluating a symbol different from the optimized one *)
     destruct (lookup ini_sfs_map symbol) as [symbolexpr|] eqn: eqlookupsymbol.
     * (* lookup ini_sfs_map = Some symbolexpr *)
       pose proof (opt_add_zero_only_affects_symbol absi abso opt_absi opt_abso
          ini_sfs_map opt_sfs_map symbol_opt Hopt) as Hupdate_opt.
       destruct Hupdate_opt as [symb_sfs_expr Hopt_sfs_map].
       rewrite -> Hopt_sfs_map.
       rewrite -> update_lookup_diff; try assumption.
       rewrite -> eqlookupsymbol.
       (* Folding/unfolding of SFS to apply the IH *)
       rewrite <- eqini_sfs in Hdisjoint.
       rewrite <- eqini_sfs in Hopt.
       rewrite <- eqopt_sfs in Hopt.
       rewrite <- eqini_sfs.
       rewrite <- Hopt_sfs_map.
       rewrite <- eqopt_sfs.
       destruct symbolexpr as [value|name|op name1 name2] eqn: eqsfsexpr.
       -- reflexivity.
       -- fold evaluate_sfs_from_map.
          pose proof (IH stack ini_sfs opt_sfs symbol_opt name 
            Hdisjoint Hopt) as IHname.
          assumption.
       -- fold evaluate_sfs_from_map.
          pose proof (IH stack ini_sfs opt_sfs symbol_opt name1
            Hdisjoint Hopt) as IHname1.
          rewrite <- IHname1.
          pose proof (IH stack ini_sfs opt_sfs symbol_opt name2
            Hdisjoint Hopt) as IHname2.
          rewrite <- IHname2.
          reflexivity.
     * (* lookup ini_sfs_map = None *)
       pose proof (optimize_add_zero_same_but_symb symbol_opt symbol
         absi abso opt_absi opt_abso ini_sfs_map opt_sfs_map eqsymbolopt Hopt) 
         as Hlookup.
       rewrite -> Hlookup in eqlookupsymbol.
       rewrite -> eqlookupsymbol.
       reflexivity.
Qed.



(************
  OPTIMIZATION X*1 -> X
  TODO: proofs
 ************)

Definition WOne: EVMWord  := natToWord WLen 1.

(* MUL(X, 1) -> X and MUL(1, X) -> X *)
Definition optimize_mul_one (var: string) (s: sfs) : option sfs :=
match s with
 | SFS absi abso smap => 
     match lookup smap var with
      | Some (SFSbinop (SimplePriceOpcodeMk MUL) a b) =>
          if points_to_const a smap WOne then Some (SFS absi abso (update smap var (SFSname b)))
          else if points_to_const b smap WOne then Some (SFS absi abso (update smap var (SFSname a)))
          else None
      | _ => None
     end
end.

Example ex_mul1:
match abstract_eval 0 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WOne)::
                     SimplePriceOpcodeMk MUL::
                     nil) with
 | Some (SFS absi abso smap) => optimize_mul_one "e0" (SFS absi abso smap)
 | _ => None
end = None. (* e0 is just WOne*)
Proof. reflexivity. Qed.

Example ex_mul2:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WOne)::
                     SimplePriceOpcodeMk MUL::
                     nil) with
 | Some (SFS absi abso smap) => optimize_mul_one "e1" (SFS absi abso smap)
 | _ => None
end = 
Some (SFS ("s0"::nil) ("e1"::nil)
          (("e1", SFSname "s0")::
           ("e1", SFSbinop (SimplePriceOpcodeMk MUL) "e0" "s0")::
           ("e0", SFSconst WOne)::nil)).
Proof. reflexivity. Qed.

Example ex_mul3:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) WOne)::
                      SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 7))::
                      SimplePriceOpcodeMk MUL::
                      nil) with
 | Some (SFS absi abso smap) => optimize_mul_one "e2" (SFS absi abso smap)
 | _ => None
end = 
Some (SFS ("s0"::nil) ("e2"::"s0"::nil)
          (("e2", SFSname "e1")::
           ("e2", SFSbinop (SimplePriceOpcodeMk MUL) "e1" "e0")::
           ("e1", SFSconst (natToWord WLen 7))::
           ("e0", SFSconst WOne)::nil)).
Proof. reflexivity. Qed.

Example ex_mul4:
match abstract_eval 1 (SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 2))::
                      SimplePriceOpcodeMk (PUSH (natToWord 5 0) (natToWord WLen 7))::
                      SimplePriceOpcodeMk MUL::
                      nil) with
 | Some (SFS absi abso smap) => optimize_mul_one "e2" (SFS absi abso smap)
 | _ => None
end = None. (* the multiplication in e2 is 7 * 2 *)
Proof. reflexivity. Qed.



Theorem optimize_mul_one_correct: forall (d: nat) 
        (concrete_stack: map EVMWord) (ini_sfs opt_sfs: sfs) 
        (symbol_opt symbol: string),
disjoint_stack_sfs concrete_stack ini_sfs ->
optimize_mul_one symbol_opt ini_sfs = Some opt_sfs ->
evaluate_sfs_from_map d concrete_stack ini_sfs symbol = 
evaluate_sfs_from_map d concrete_stack opt_sfs symbol.
Proof. Admitted.

