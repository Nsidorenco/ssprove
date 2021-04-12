
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
  Notation " 'chInput' " := (chProd (chProd choiceStatement choiceWitness) choiceChallenge) (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chChallenge' " := choiceChallenge (in custom pack_type at level 2).
  Notation " 'chCommit' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chOpen' " := (chProd choiceChallenge choiceResponse) (in custom pack_type at level 2).
  Notation " 'chTranscript' " := choiceTranscript (in custom pack_type at level 2).
  Definition i_witness := #|Witness|.
  Definition i_challenge := #|Challenge|.
  Definition RUN : nat := 0.
  Definition COM : nat := 1.
  Definition VER : nat := 2.
  Definition HIDING : nat := 3.

  (* Commitment scheme specific *)
  Notation " 'chBool' " := 'fin #|bool_choiceType| (in custom pack_type at level 2).
  Notation " 'chOpen' " := (chProd (chProd (chProd choiceStatement choiceWitness) 'option choiceTranscript) choiceChallenge) (in custom pack_type at level 2).
  Notation " 'chRel' " := (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).

  Definition Bool_pos : Positive #|bool_choiceType|.
  Proof. rewrite card_bool. done. Qed.
  #[local] Existing Instance Bool_pos.

  Definition i_challenge_pos : Positive i_challenge.
  Proof. unfold i_challenge. apply Challenge_pos. Qed.
  #[local] Existing Instance i_challenge_pos.


  Local Open Scope package_scope.

  Definition RUN_real:
    package fset0
      [interface]
      [interface val #[ RUN ] : chInput → 'option chTranscript] :=
    [package
     def #[ RUN ] (hwe: chInput) : 'option chTranscript
      {
        let '(h,w,e) := hwe in
        if (R (otf h) (otf w)) then
          m ← Commit h w ;;
          let '(a, s) := m in
          z ← Response h w s a e ;;
          ret (Some (a,e,z))
        else ret None
      }
    ].
  
  Definition RUN_ideal:
    package fset0
      [interface]
      [interface val #[ RUN ] : chInput → 'option chTranscript] :=
    [package
     def #[ RUN ] (hwe: chInput) : 'option chTranscript
      {
        let '(h, w, e) := hwe in
        if (R (otf h) (otf w)) then
          t ← Simulate h e ;;
          ret (Some t)
        else ret None
      }
    ].
  
  Definition SHVZK:
    loc_GamePair [interface val #[ RUN ] : chInput → 'option chTranscript] :=
    fun b => if b then {locpackage RUN_ideal} else {locpackage RUN_real }.

  Definition Sigma_to_Com:
    package fset0
      [interface val #[ RUN ] : chInput → 'option chTranscript]
      [interface val #[ COM ] : chInput → 'option chTranscript] :=
                 (* val #[ VER ] : chOpen → chBool] := *)
    [package
     def #[ COM ] (hwe : chInput) : 'option chTranscript
     {
       #import {sig #[ RUN ] : chInput → 'option chTranscript} as run ;;
       t ← run hwe ;;
       ret t
     }
     (* ; *)
     (* def #[ VER ] (open : chOpen) : chBool *)
     (* { *)
     (*   #import {sig #[ VER ] : chOpen → chBool} as ver ;; *)
     (*   b ← ver open ;; *)
     (*   ret b *)
     (* } *)
    ].

  (* Commitment to input value*)
  Definition Hiding_real :
    package fset0
      [interface val #[ COM ] : chInput → 'option chTranscript]
                 (* val #[ VER ] : chOpen → chBool]  *)
      [interface val #[ HIDING ] : chInput → 'option chMessage] :=
    [package
     def #[ HIDING ] (hwe : chInput) : 'option chMessage
     {
       #import {sig #[ COM ] : chInput → 'option chTranscript} as com ;;
       _ ← sample uniform i_challenge ;;
       t ← com hwe ;;
       match t with
         | Some (a,e,z) => ret (Some a)
         | _ => ret None
       end
     }
    ].
             
  (* Commitment to random value *)
  Definition Hiding_ideal :
    package fset0
      [interface val #[ COM ] : chInput → 'option chTranscript]
                 (* val #[ VER ] : chOpen → chBool] *)
      [interface val #[ HIDING ] : chInput → 'option chMessage] :=
    [package
     def #[ HIDING ] (hwe : chInput) : 'option chMessage
     {
       #import {sig #[ COM ] : chInput → 'option chTranscript} as com ;;
       let '(h,w,_) := hwe in
       e ← sample uniform i_challenge ;;
       t ← com (h,w,e) ;;
       match t with
         | Some (a,e,z) => ret (Some a)
         | _ => ret None
       end
     }
    ].

Definition aux_hiding A :=
  AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK false) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK false) A.
(* Proof. *)
(*   apply eq_rel_perf_ind_eq. *)

(*   rewrite !link_assoc. *)
(*   (* set M := Sigma_to_Com ∘ SHVZK true. *) *)
(*   unfold eq_up_to_inv. *)
(*   move=> id S T x H. *)
(*   rewrite rel_jdgE. *)
(*   rewrite !get_op_default_link. *)
(*   invert_interface_in H. *)
(*   erewrite ?get_op_default_spec. *)
(*   2,3: intuition. *)
(*   destruct x as [[h w] x]. *)
(*   rewrite -rel_jdgE. *)
(*   cbn. *)
(*   chUniverse_eqP_handle. *)
(*   chUniverse_eqP_handle. *)
(*   cbn. *)
(*   chUniverse_eqP_handle. *)
(*   chUniverse_eqP_handle. *)
(*   cbn. *)
(*   eapply r_uniform_bij. *)
(*   1:{ pose f := fun (e : choiceChallenge) => e. *)
(*       assert (bij_f : bijective f). *)
(*       1: exists id; intro e; trivial.  *)
(*       exact bij_f. } *)
(*   move=> e. *)
(*   case_eq (R (otf h) (otf w))=> rel. *)
(*   1: { unfold Simulate. *)
(*   1: { *)

    
(*        eapply rconst_samplerL. *)

(*   simplify_eq_rel hw. *)
(*   ssprove_code_link_commute. *)
(*   simplify_linking. *)

(* Admitted. *)


Theorem commitment_hiding :
  ∀ LA A eps,
    ValidPackage LA [interface val #[ HIDING ] : chInput → 'option chMessage] A_export A →
    (∀ A',
      ValidPackage LA [interface val #[ RUN ] : chInput → 'option chTranscript] A_export A' →
      Advantage SHVZK A' <= eps) →
    AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A <= (aux_hiding A) + eps + eps.
Proof.
  intros LA A eps Va Hadv.
  pose proof (
         Advantage_triangle_chain (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) [::
           (Hiding_real ∘ Sigma_to_Com ∘ SHVZK false) ;
           (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK false)
         ] (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A
       ) as ineq.
  advantage_sum simpl in ineq.
  rewrite !GRing.addrA in ineq.
  apply: ler_trans. 1: exact ineq.
  clear ineq.
  unfold aux_hiding.
  (* 2,3 : by rewrite !fdisjointUr fdisjoints0. *)
  rewrite -!Advantage_link.
  eapply ler_add. 
  1: rewrite GRing.addrC; eapply ler_add.
  1: apply lerr.
  - have := Hadv (A ∘ Hiding_real ∘ Sigma_to_Com).
    assert (ValidPackage LA [interface val #[RUN] : chInput → 'option (chTranscript) ] A_export (A ∘ Hiding_real ∘ Sigma_to_Com)).
    + rewrite link_assoc.
      have -> : LA = (LA :|: fset0) by rewrite fsetU0.
      eapply valid_link with [interface val #[ COM ] : chInput → 'option chTranscript].
      2 : { apply valid_package_from_class; intuition. }
      have -> : LA = (LA :|: fset0) by rewrite fsetU0.
      eapply valid_link with [interface val #[ HIDING ] : chInput → 'option chMessage].
      all : apply valid_package_from_class; intuition.
    + move=> Hadv'.
      apply Hadv' in H.
      rewrite Advantage_sym -link_assoc.
      assumption.
  - have := Hadv (A ∘ Hiding_ideal ∘ Sigma_to_Com).
    assert (ValidPackage LA [interface val #[RUN] : chInput → 'option (chTranscript) ] A_export (A ∘ Hiding_ideal ∘ Sigma_to_Com)).
    + rewrite link_assoc.
      have -> : LA = (LA :|: fset0) by rewrite fsetU0.
      eapply valid_link with [interface val #[ COM ] : chInput → 'option chTranscript].
      2 : { apply valid_package_from_class; intuition. }
      have -> : LA = (LA :|: fset0) by rewrite fsetU0.
      eapply valid_link with [interface val #[ HIDING ] : chInput → 'option chMessage].
      all : apply valid_package_from_class; intuition.
    + move=> Hadv'.
      apply Hadv' in H.
      rewrite -link_assoc.
      assumption.
Qed.

End SigmaProtocol.
