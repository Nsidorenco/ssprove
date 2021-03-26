
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition chUniverse pkg_composition pkg_rhl Package Prelude
  pkg_notation AsymScheme.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Parameter gT : finGroupType.
Definition ζ : {set gT} := [set : gT].
Parameter g :  gT.
Parameter g_gen : ζ = <[g]>.
Parameter prime_order : prime #[g].

Lemma cyclic_zeta: cyclic ζ.
Proof.
  apply /cyclicP. exists g. exact: g_gen.
Qed.

(* order of g *)
Definition q : nat := #[g].

Lemma group_prodC :
  ∀ x y : gT, x * y = y * x.
Proof.
  move => x y.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  subst.
  repeat rewrite -expgD addnC. reflexivity.
Qed.

Lemma group_prodA :
  ∀ x y z : gT, x * (y * z) = (x * y) * z.
Proof.
  move => x y z.
  have Hx: exists ix, x = g^+ix.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hy: exists iy, y = g^+iy.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  have Hz: exists iz, z = g^+iz.
  { apply /cycleP. rewrite -g_gen.
    apply: in_setT. }
  destruct Hx as [ix Hx].
  destruct Hy as [iy Hy].
  destruct Hz as [iz Hz].
  subst.
  repeat rewrite -expgD addnC addnA.
  rewrite mulgA.
  reflexivity.
Qed.

Inductive probEmpty : Type → Type := .

Module Type SigmaProtocolParams.

  Parameter Witness Statement Message Challenge Response State : finType.
  Parameter w0 : Witness.
  Parameter e0 : Challenge.
  Parameter z0 : Response.
  Parameter R : Statement -> Witness -> bool.

End SigmaProtocolParams.

Module Type SigmaProtocolRules (π : SigmaProtocolParams).

  Import π.

End SigmaProtocolRules.

Module SchnorrParams <: SigmaProtocolParams.

  Definition Witness : finType := [finType of 'Z_q].
  Definition Statement : finType := FinGroup.arg_finType gT.
  Definition Message : finType := FinGroup.arg_finType gT.
  Definition Challenge : finType := [finType of 'Z_q].
  Definition Response : finType :=  [finType of 'Z_q].
  Definition Transcript := prod_finType (prod_finType Message Challenge) Response.
  Definition State := Witness.

  Definition w0 : Witness := 0.
  Definition e0 : Challenge := 0.
  Definition z0 : Response := 0.

  Definition R : Statement -> Witness -> bool :=
    (fun (h : Statement) (w : Witness) => h == (g ^+ w)).

End SchnorrParams.

Local Open Scope package_scope.

Import SchnorrParams.

Include (SigmaProtocolRules SchnorrParams).

Import PackageNotation.

Instance positive_gT : Positive #|gT|.
Proof.
  apply /card_gt0P. exists g. auto.
Qed.

Instance positive_Witness : Positive #|Witness|.
Proof.
  apply /card_gt0P. exists w0. auto.
Qed.

Definition choiceWitness : chUniverse := 'fin #|Witness|.
Definition choiceStatement : chUniverse := 'fin #|Statement|.
Definition choiceMessage : chUniverse := 'fin #|Message|.
Definition choiceChallenge : chUniverse := 'fin #|Challenge|.
Definition choiceResponse : chUniverse := 'fin #|Response|.
Definition choiceTranscript : chUniverse := chProd (chProd choiceMessage choiceChallenge) choiceResponse.
Definition choiceState := choiceWitness.

Definition i_witness := #|Witness|.
Definition i_challenge := #|Challenge|.
  
Definition INIT : nat := 3.
Definition CHALLENGE : nat := 4.
Definition RESPONSE : nat := 5.
Definition VERIFY : nat := 6.
Definition SIM : nat := 7.
Definition RUN : nat := 8.

Notation " 'chStatement' " :=
  choiceStatement
  (in custom pack_type at level 2).
Notation " 'chMessage' " :=
  choiceMessage
  (in custom pack_type at level 2).
Notation " 'chCommit' " :=
  (chProd choiceMessage choiceState)
  (in custom pack_type at level 2).
Notation " 'chChallenge' " :=
  choiceChallenge
  (in custom pack_type at level 2).
Notation " 'chResponse' " :=
  choiceResponse
  (in custom pack_type at level 2).
Notation " 'chFst' " :=
  (chProd (chProd choiceMessage choiceState) choiceChallenge)
  (in custom pack_type at level 2).
Notation " 'chTranscript' " :=
  choiceTranscript
  (in custom pack_type at level 2).

Definition SigmaProtocol (h : choiceStatement) (w : choiceWitness):
  package fset0
  [interface]
  [interface val #[ INIT ] : 'unit → chCommit ;
             (* val #[ CHALLENGE ] : chMessage → chChallenge ; *)
             val #[ RESPONSE ] : chFst → chResponse
             (* val #[ VERIFY ] : chTranscript → 'bool *)
  ] :=
  [package
    def #[ INIT ] (_ : 'unit) : chCommit {
     r ← sample uniform i_witness ;;
     ret (fto (g ^+ (otf r)), r)
    } ;

    (* def #[ CHALLENGE ] (a : chMessage) : chChallenge { *)
    (*  e ← sample uniform i_challenge ;; *)
    (*  ret e *)
    (* } ; *)

    def #[ RESPONSE ] (are : chFst) : chResponse {
     let '(tmp,e) := are in
     let '(a,r) := tmp in
     ret (fto (otf r + otf e * otf w))
    } 
  ].

Definition Simulator (h : choiceStatement):
  package fset0
   [interface]
   [interface val #[ SIM ] : chChallenge → chTranscript] :=
  [package
   def #[ SIM ] (e : chChallenge) : chTranscript {
     z ← sample uniform i_witness ;;
     ret (fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z)
  }].

Definition RUN_real (e : choiceChallenge):
  package fset0
    [interface val #[ INIT ] : 'unit → chCommit ;
               val #[ RESPONSE ] : chFst → chResponse ]
    [interface val #[ RUN ] : 'unit → chTranscript] :=
  [package
   def #[ RUN ] (_: 'unit) : chTranscript
    {
      #import {sig #[ INIT ] : 'unit → chCommit } as msg ;;
      #import {sig #[ RESPONSE ] : chFst → chResponse } as rspns ;;
      m ← msg Datatypes.tt ;;
      let '(a, r) := m in
      z ← rspns (m, e) ;;
      ret (a,e,z)
    }
  ].

Definition RUN_ideal (e : choiceChallenge):
  package fset0
    [interface val #[ SIM ] : chChallenge → chTranscript ]
    [interface val #[ RUN ] : 'unit → chTranscript] :=
  [package
   def #[ RUN ] (_: 'unit) : chTranscript
    {
      #import {sig #[ SIM ] : chChallenge → chTranscript } as sim ;;
      t ← sim e ;;
      ret t
    }
  ].

Definition SHVZK h w e :
  loc_GamePair [interface val #[ RUN ] : 'unit → chTranscript] :=
  fun b => if b then {locpackage (RUN_real e ∘ (SigmaProtocol h w))} else {locpackage (RUN_ideal e ∘ (Simulator h))}.

#[local] Definition f (e w : Witness) :
  Arit (uniform i_witness) → Arit (uniform i_witness) :=
  fun z => fto ((otf z) + e * w).

Lemma order_ge1 : g ^+ succn (succn (Zp_trunc q)) = g ^+ q.
Proof.
  rewrite Zp_cast.
  - reflexivity.
  - apply prime_gt1, prime_order. 
Qed.

Lemma real_ideal_equiv h w e:
  R (otf h) (otf w) = true ->
  (SHVZK h w e) true ≈₀ (SHVZK h w e) false.
Proof.
  unfold R=> rel. apply reflection_nonsense in rel.
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_link_commute. simpl.
  simplify_linking.
  (* Programming logic part *)
  pose f' := f (otf e) (otf w).
  assert (bij_f : bijective f').
  { subst f'. unfold f.
    exists (fun x => (fto (otf x - (otf e) * (otf w)))).
    - intro x; unfold fto, otf; rewrite !enum_rankK GRing.addrK enum_valK; reflexivity. 
    - intro x; unfold fto, otf; rewrite !enum_rankK GRing.subrK enum_valK; reflexivity.
  }
  eapply r_uniform_bij with (1 := bij_f)=> z_val.
  apply r_ret.
  (* Ambient logic proof of post condition *)
  intros s0 s1 Hs.
  unfold f', f.
  rewrite -!expgnE rel.
  split.
  2: apply Hs. 
  simpl. f_equal.
  rewrite otf_fto expg_mod.
  2: rewrite order_ge1; apply expg_order.
  rewrite expgD -!expgVn.
  rewrite group_prodC group_prodA group_prodC group_prodA /=.
  rewrite expg_mod.
  2 : rewrite order_ge1; apply expg_order.
  rewrite expgM expgAC -!expgM -expgMn.
  - rewrite mulgV expg1n mul1g. reflexivity.
  - apply group_prodC.
Qed.
