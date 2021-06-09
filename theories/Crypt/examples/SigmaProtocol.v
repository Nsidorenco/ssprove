
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
  Parameter Bool_pos : Positive #|bool_choiceType|.

  #[local] Existing Instance Bool_pos.
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
  Definition choiceBool := 'fin #|bool_choiceType|.

  Parameter Sigma_locs : {fset Location}.
  Parameter Simulator_locs : {fset Location}.

  Parameter Commit :
    ∀ (h : choiceStatement) (w : choiceWitness),
      code Sigma_locs [interface] (choiceMessage × choiceState).

  Parameter Response :
    ∀ (h : choiceStatement) (w : choiceWitness) (s : choiceState) (a : choiceMessage) (e : choiceChallenge),
      code Sigma_locs [interface] choiceResponse.

  Parameter Verify :
    ∀ (h : choiceStatement) (a : choiceMessage) (e : choiceChallenge) (z : choiceResponse),
      code Sigma_locs [interface] choiceBool.

  Parameter Simulate :
    ∀ (h : choiceStatement) (e : choiceChallenge),
      code Simulator_locs [interface] choiceTranscript.

  Parameter Extractor :
    ∀ (h : choiceStatement) (a : choiceMessage)
      (e : choiceChallenge) (e' : choiceChallenge)
      (z : choiceResponse)  (z' : choiceResponse), 'option choiceWitness.

  (*TODO: Add Challenge, Verify, and Extractor procedures. *)

  Notation " 'chStatement' " := choiceStatement (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
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
  Notation " 'chStatement' " := choiceStatement (in custom pack_type at level 2).
  Notation " 'chInput' " := (chProd (chProd choiceStatement choiceWitness) choiceChallenge) (in custom pack_type at level 2).
  Notation " 'chMessage' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chChallenge' " := choiceChallenge (in custom pack_type at level 2).
  Notation " 'chCommit' " := choiceMessage (in custom pack_type at level 2).
  Notation " 'chTranscript' " := choiceTranscript (in custom pack_type at level 2).
  Notation " 'chSoundness' " := (chProd choiceStatement
                                  (chProd choiceMessage
                                    (chProd (chProd choiceChallenge choiceChallenge)
                                            (chProd choiceResponse choiceResponse)))) (in custom pack_type at level 2).
  Definition i_witness := #|Witness|.
  Definition i_challenge := #|Challenge|.
  Definition RUN : nat := 0.
  Definition COM : nat := 1.
  Definition VER : nat := 2.
  Definition SOUNDNESS : nat := 3.
  Definition HIDING : nat := 4.
  Definition ADV : nat := 5.

  (* Commitment scheme specific *)
  Notation " 'chBool' " := choiceBool (in custom pack_type at level 2).
  Notation " 'chOpen' " := (chProd choiceStatement 'option choiceTranscript) (in custom pack_type at level 2).
  Notation " 'chRel' " := (chProd choiceStatement choiceWitness) (in custom pack_type at level 2).

  Definition Opening := chProd choiceChallenge choiceResponse.

  Notation " 'chBinding' " := (chProd choiceMessage (chProd Opening Opening))
                                (in custom pack_type at level 2).

  Definition i_challenge_pos : Positive i_challenge.
  Proof. unfold i_challenge. apply Challenge_pos. Qed.
  #[local] Existing Instance i_challenge_pos.

  Local Open Scope package_scope.

  Definition RUN_real:
    package Sigma_locs
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
    package Simulator_locs
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

  (* Type checking fails on this. *)
  (* Most likely due to interface mismatch between Sigma_to_com and Verify. *)
  (* Verify does not import any packages. So this should not be a problem? *)
  Definition Verify' :
    ∀ {L} (h : choiceStatement) (a : choiceMessage) (e : choiceChallenge) (z : choiceResponse),
      code Sigma_locs L choiceBool.
  Proof.
    intros L h a e z.
    have H := @Verify h a e z.
    eapply mkprog with H.
    eapply valid_injectMap.
    2: apply H.
    rewrite -fset0E.
    apply fsub0set. 
  Defined.

  Definition Sigma_to_Com:
    package Sigma_locs
      [interface val #[ RUN ] : chInput → 'option chTranscript]
      [interface val #[ COM ] : chInput → 'option chTranscript ;
                 val #[ VER ] : chOpen → chBool] :=
    [package
     def #[ COM ] (hwe : chInput) : 'option chTranscript
     {
       #import {sig #[ RUN ] : chInput → 'option chTranscript} as run ;;
       t ← run hwe ;;
       ret t
     }
     ;
     def #[ VER ] (open : chOpen) : chBool
     {
       match open with
         | (h, Some (a,e,z)) => Verify' h a e z
         | _ => ret (fto false)
       end
     }
    ].

  (* Commitment to input value*)
  Definition Hiding_real :
    package Sigma_locs
      [interface val #[ COM ] : chInput → 'option chTranscript ;
                 val #[ VER ] : chOpen → chBool]
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
    package Sigma_locs
      [interface val #[ COM ] : chInput → 'option chTranscript ;
                 val #[ VER ] : chOpen → chBool]
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

  Definition ɛ_hiding A :=
    AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK false) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK false) A.
  
  Theorem commitment_hiding :
    ∀ LA A eps,
      ValidPackage LA [interface val #[ HIDING ] : chInput → 'option chMessage] A_export A →
      (∀ A',
        ValidPackage (fsetU LA Sigma_locs) [interface val #[ RUN ] : chInput → 'option chTranscript] A_export A' →
        Advantage SHVZK A' <= eps) →
      AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A <= (ɛ_hiding A) + eps + eps.
  Proof.
    intros LA A eps Va Hadv.
    ssprove triangle (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) [::
             (Hiding_real ∘ Sigma_to_Com ∘ SHVZK false) ;
             (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK false)
           ] (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A
      as ineq.
    apply: ler_trans. 1: exact ineq.
    clear ineq.
    unfold ɛ_hiding.
    (* 2,3 : by rewrite !fdisjointUr fdisjoints0. *)
    rewrite -!Advantage_link.
    eapply ler_add. 
    1: rewrite GRing.addrC; eapply ler_add.
    1: apply lerr.
    - have := Hadv (A ∘ Hiding_real ∘ Sigma_to_Com).
      assert (ValidPackage (fsetU LA Sigma_locs) [interface val #[RUN] : chInput → 'option (chTranscript) ] A_export (A ∘ Hiding_real ∘ Sigma_to_Com)).
      + rewrite link_assoc.
        have -> : LA :|: Sigma_locs = LA :|: Sigma_locs :|: Sigma_locs.
        { rewrite - fsetUA fsetUid. reflexivity. }
        eapply valid_link with [interface val #[ COM ] : chInput → 'option chTranscript ;
                                          val #[ VER ] : chOpen → chBool].
        2 : { apply valid_package_from_class; apply Sigma_to_Com. }
        eapply valid_link with [interface val #[ HIDING ] : chInput → 'option chMessage].
        ++ assumption.
        ++ apply Hiding_real.
      + move=> Hadv'.
        apply Hadv' in H.
        rewrite Advantage_sym -link_assoc.
        assumption.
    - have := Hadv (A ∘ Hiding_ideal ∘ Sigma_to_Com).
      assert (ValidPackage (fsetU LA Sigma_locs) [interface val #[RUN] : chInput → 'option (chTranscript) ] A_export (A ∘ Hiding_ideal ∘ Sigma_to_Com)).
      + rewrite link_assoc.
        have -> : LA :|: Sigma_locs = LA :|: Sigma_locs :|: Sigma_locs.
        { rewrite - fsetUA fsetUid. reflexivity. }
        eapply valid_link with [interface val #[ COM ] : chInput → 'option chTranscript ;
                                          val #[ VER ] : chOpen → chBool].
        2 : { apply valid_package_from_class; apply Sigma_to_Com. }
        eapply valid_link with [interface val #[ HIDING ] : chInput → 'option chMessage].
        ++ assumption.
        ++ apply Hiding_ideal.
      + move=> Hadv'.
        apply Hadv' in H.
        rewrite -link_assoc.
        assumption.
  Qed.

  Definition Special_Soundness_f:
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chBinding]
      [interface val #[ SOUNDNESS ] : chStatement → chBool] :=
    [package
     def #[ SOUNDNESS ] (h : chStatement) : chBool
      {
        #import {sig #[ ADV ] : chStatement → chBinding} as A ;;
        '(a, tmp) ← A(h) ;;
        let '(c1, c2) := tmp in
        let '(e, z) := c1 in
        let '(e', z') := c2 in
        v1 ← Verify' h a e z ;;
        v2 ← Verify' h a e' z' ;;
        if (andb (e != e') (andb (otf v1) (otf v2))) then
            match Extractor h a e e' z z' with
            | Some w => ret (fto (R (otf h) (otf w)))
            | None => ret (fto false)
            end
        else ret (fto false)
      }
    ].

  Definition Special_Soundness_t:
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chBinding]
      [interface val #[ SOUNDNESS ] : chStatement → chBool] :=
    [package
     def #[ SOUNDNESS ] (h : chStatement) : chBool
      {
        #import {sig #[ ADV ] : chStatement → chBinding} as A ;;
        '(a, tmp) ← A h ;;
        let '(c1, c2) := tmp in
        let '(e, z) := c1 in
        let '(e', z') := c2 in
        v1 ← Verify' h a e z ;;
        v2 ← Verify' h a e' z' ;;
        if (andb (e != e') (andb (otf v1) (otf v2))) then
            ret (fto true)
        else ret (fto false)
      }
    ].

  Definition ɛ_soundness A Adv := AdvantageE (Special_Soundness_t ∘ Adv) (Special_Soundness_f ∘ Adv) A.

  Definition Com_Binding:
    package Sigma_locs
      [interface val #[ ADV ] : chStatement → chBinding]
      [interface val #[ SOUNDNESS ] : chStatement → chBool] :=
    [package
     def #[ SOUNDNESS ] (h : chStatement) : chBool
      {
        #import {sig #[ ADV ] : chStatement → chBinding} as A ;;
        '(a, tmp) ← A h ;;
        let '(c1, c2) := tmp in
        let '(e, z) := c1 in
        let '(e', z') := c2 in
        v1 ← Verify' h a e z;;
        v2 ← Verify' h a e' z' ;;
        ret (fto (andb (e != e') (andb (otf v1) (otf v2))))
      }
    ].

  Ltac invalid_adv :=
    rewrite ?code_link_bind;
    apply rsame_head=> ?;
    apply rsame_head=> ?;
    rewrite !code_link_scheme;
    apply r_ret; auto.

  Lemma binding:
    ∀ LA A LAdv Adv,
      ValidPackage LA [interface val #[ SOUNDNESS ] : chStatement → chBool] A_export A →
      ValidPackage LAdv [interface] [interface val #[ ADV ] : chStatement → chBinding] Adv →
      fdisjoint LA (Sigma_locs :|: LAdv) →
      AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <= (ɛ_soundness A Adv).
    intros LA A LAdv Adv VA VAdv Hdisj.
    ssprove triangle (Com_Binding ∘ Adv) [::
             (Special_Soundness_t ∘ Adv)
           ] (Special_Soundness_f ∘ Adv) A as ineq.
    apply: ler_trans. 1: exact ineq.
    rewrite ger_addr.

    assert (AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_t ∘ Adv) A = 0) as ɛ_Adv.
    2: rewrite ɛ_Adv; apply lerr.

    eapply eq_rel_perf_ind_eq.
    4: apply VA.
    1,2: eapply valid_link; last first; [apply VAdv | trivial].
    1: apply Com_Binding.
    1: apply Special_Soundness_t.
    2,3: assumption.

    intros id So To m hin.
    invert_interface_in hin.
    unfold get_op_default.
    destruct lookup_op as [f|] eqn:e.
    2: { exfalso.
         simpl in e.
         chUniverse_eqP_handle.
         chUniverse_eqP_handle.
         inversion e.
    }
    simpl in e.
    chUniverse_eqP_handle.
    chUniverse_eqP_handle.
    rewrite cast_fun_K in e.
    inversion e.

    clear e H0.

    destruct lookup_op as [f0|] eqn:e.
    2: { exfalso.
         simpl in e.
         chUniverse_eqP_handle.
         chUniverse_eqP_handle.
         inversion e.
    }
    simpl in e.
    chUniverse_eqP_handle.
    chUniverse_eqP_handle.
    rewrite cast_fun_K in e.
    inversion e.

    clear e H0.

    destruct (Adv ADV).
    2: invalid_adv.
    destruct t, s.
    repeat destruct chUniverse_eqP.
    2,3: invalid_adv.
    apply rsame_head=> run.
    destruct run.
    destruct s0.
    destruct s0, s1.

    rewrite !code_link_bind.
    apply rsame_head=> v1.

    rewrite !code_link_bind.
    apply rsame_head=> v2.

    rewrite code_link_if.
    rewrite !code_link_scheme.


    match goal with
        | [ |- context[if ?b then _ else _]] => case b
    end.

    all: apply r_ret; auto.
  Qed.

End SigmaProtocol.
