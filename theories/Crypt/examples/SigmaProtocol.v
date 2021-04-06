
From Relational Require Import OrderEnrichedCategory GenericRulesSimple.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition chUniverse pkg_composition pkg_rhl
  Package Prelude.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import mc_1_10.Num.Theory.

Import PackageNotation.

Local Open Scope ring_scope.

Module Type SigmaProtocolParams.

  Parameter Witness Statement Message Challenge Response State : finType.
  Parameter w0 : Witness.
  Parameter e0 : Challenge.
  Parameter z0 : Response.
  Parameter R : Statement -> Witness -> bool.

End SigmaProtocolParams.

Module Type SigmaProtocolAlgorithms (π : SigmaProtocolParams).

  Import π.

  Local Open Scope package_scope.

  Parameter Statement_pos : Positive #|Statement|.
  Parameter Witness_pos : Positive #|Witness|.
  Parameter Message_pos : Positive #|Message|.
  Parameter Challenge_pos : Positive #|Challenge|.
  Parameter Response_pos : Positive #|Response|.
  Parameter State_pos : Positive #|State|.

  #[local] Existing Instance Statement_pos.
  #[local] Existing Instance Witness_pos.
  #[local] Existing Instance Message_pos.
  #[local] Existing Instance Challenge_pos.
  #[local] Existing Instance Response_pos.
  #[local] Existing Instance State_pos.

  Definition choiceWitness : chUniverse := 'fin #|Witness|.
  Definition choiceStatement : chUniverse := 'fin #|Statement|.
  Definition choiceMessage : chUniverse := 'fin #|Message|.
  Definition choiceChallenge : chUniverse := 'fin #|Challenge|.
  Definition choiceResponse : chUniverse := 'fin #|Response|.
  Definition choiceTranscript : chUniverse := chProd (chProd choiceMessage choiceChallenge) choiceResponse.
  Definition choiceState := 'fin #|State|.

  Parameter Commit :
    ∀ {L : {fset Location}} (h : choiceStatement) (w : choiceWitness),
      code L [interface] (choiceMessage × choiceState).

  Parameter Response :
    ∀ {L : {fset Location}} (h : choiceStatement) (w : choiceWitness) (s : choiceState) (a : choiceMessage) (e : choiceChallenge),
      code L [interface] choiceResponse.

  Parameter Simulate :
    ∀ {L : {fset Location}} (h : choiceStatement) (e : choiceChallenge),
      code L [interface] choiceTranscript.

  (*TODO: Add Challenge, Verify, and Extractor procedures. *)

  Notation " 'chStatement' " := choiceStatement (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chCommit' " := (chProd choiceMessage choiceState) (in custom pack_type at level 2).
  Notation " 'chResponse' " := choiceResponse (in custom pack_type at level 2).
  Notation " 'chFst' " :=
    (chProd (chProd choiceMessage choiceState) choiceChallenge)
      (in custom pack_type at level 2).

End SigmaProtocolAlgorithms.

Module SigmaProtocol (π : SigmaProtocolParams)
                     (Alg : SigmaProtocolAlgorithms π).

  Import π.
  Import Alg.

  (* Compatibitlity *)
  Notation " 'chInput' " := (chProd choiceStatement choiceChallenge) (in custom pack_type at level 2).
  Notation " 'chChallenge' " := choiceChallenge (in custom pack_type at level 2).
  Notation " 'chCommit' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chOpen' " := (chProd choiceChallenge choiceResponse) (in custom pack_type at level 2).
  Notation " 'chTranscript' " := choiceTranscript (in custom pack_type at level 2).
  Definition i_witness := #|Witness|.
  Definition RUN : nat := 0.
  Definition COM : nat := 1.
  Definition VER : nat := 2.

  (* Commitment scheme specific *)
  Notation " 'chBool' " := 'fin #|bool_choiceType| (in custom pack_type at level 2).
  Notation " 'chOpen' " := (chProd choiceTranscript choiceChallenge) (in custom pack_type at level 2).



  Local Open Scope package_scope.

  Definition RUN_real (h : choiceStatement) (w : choiceWitness) :
    package fset0
      [interface]
      [interface val #[ RUN ] : chChallenge → chTranscript] :=
    [package
     def #[ RUN ] (e: chChallenge) : chTranscript
      {
        m ← Commit h w ;;
        let '(a, s) := m in
        z ← Response h w s a e ;;
        ret (a,e,z)
      }
    ].
  
  Definition RUN_ideal (h : choiceStatement):
    package fset0
      [interface]
      [interface val #[ RUN ] : chChallenge → chTranscript] :=
    [package
     def #[ RUN ] (e: chChallenge) : chTranscript
      {
        t ← Simulate h e ;;
        ret t
      }
    ].
  
  Definition SHVZK h w :
    loc_GamePair [interface val #[ RUN ] : chChallenge → chTranscript] :=
    fun b => if b then {locpackage (RUN_ideal h)} else {locpackage (RUN_real h w)}.

  Definition CommitmentScheme_SigmaProtocol:
    package fset0
      [interface val #[ RUN ] : chChallenge → chTranscript]
      [interface val #[ COM ] : chChallenge → chTranscript ;
                 val #[ VER ] : chOpen → chBool] :=
    [package
     def #[ COM ] (e : chChallenge) : chTranscript
     {
       #import {sig #[ RUN ] : chChallenge → chTranscript} as run ;;
       t ← run e ;; ret t
     }
     ;
     def #[ VER ] (te : chOpen) : chBool
     {
       #import {sig #[ RUN ] : chChallenge → chTranscript} as run ;;
       let '(t, e) := te in
       t' ← run e ;;
       ret (otf (t == t'))
     } 
    ].

End SigmaProtocol.
