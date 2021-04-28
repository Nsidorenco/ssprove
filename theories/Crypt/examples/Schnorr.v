
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
  pkg_notation SigmaProtocol.

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

Import PackageNotation.

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

Module MyParam <: SigmaProtocolParams.

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

End MyParam.

Module MyAlg <: SigmaProtocolAlgorithms MyParam.

  Import MyParam.

  Instance positive_gT : Positive #|gT|.
  Proof.
    apply /card_gt0P. exists g. auto.
  Qed.

  Instance Witness_pos : Positive #|Witness|.
  Proof.
    apply /card_gt0P. exists w0. auto.
  Qed.

  Definition Statement_pos : Positive #|Statement| := _.
  Definition Message_pos : Positive #|Message| := _.
  Definition Challenge_pos : Positive #|Challenge| := _.
  Definition Response_pos : Positive #|Response| := _.
  Definition State_pos : Positive #|State| := _.
  
  Definition choiceWitness : chUniverse := 'fin #|Witness|.
  Definition choiceStatement : chUniverse := 'fin #|Statement|.
  Definition choiceMessage : chUniverse := 'fin #|Message|.
  Definition choiceChallenge : chUniverse := 'fin #|Challenge|.
  Definition choiceResponse : chUniverse := 'fin #|Response|.
  Definition choiceTranscript : chUniverse := chProd (chProd choiceMessage choiceChallenge) choiceResponse.
  Definition choiceState := 'fin #|State|.

  Definition i_witness := #|Witness|.

  Definition HIDING : nat := 0.

  Definition Commit {L : {fset Location}} (h : choiceStatement) (w : choiceWitness):
    code L [interface] (choiceMessage × choiceState) :=
    {code
       r ← sample uniform i_witness ;;
       ret (fto (g ^+ otf r), r)
    }.

  Definition Response {L : {fset Location}} (h : choiceStatement) (w : choiceWitness) (r : choiceState) (a : choiceMessage) (e : choiceChallenge):
    code L [interface] choiceResponse :=
    {code
       ret (fto (otf r + otf e * otf w))
    }.

  Definition Simulate {L : {fset Location}} (h : choiceStatement) (e : choiceChallenge):
    code L [interface] choiceTranscript :=
    {code
       z ← sample uniform i_witness ;;
       ret (fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z)
    }.

  #[local] Existing Instance Bool_pos.
  Definition Verify {L : {fset Location}} (h : choiceStatement) (a : choiceMessage) (e : choiceChallenge) (z : choiceResponse):
    code L [interface] 'fin #|bool_choiceType| :=
    {code
       ret (fto true)
    }.

  Definition Extractor {L : {fset Location}} (h : choiceStatement) (a : choiceMessage)
                                             (e : choiceChallenge) (e' : choiceChallenge)
                                             (z : choiceResponse)  (z' : choiceResponse) :
      code L [interface] ('option choiceWitness) :=
    {code
       ret None
    }.

End MyAlg.

Local Open Scope package_scope.

Module Schnorr := SigmaProtocol MyParam MyAlg.

Import MyParam MyAlg Schnorr.

#[local] Definition f (e w : Witness) :
  Arit (uniform i_witness) → Arit (uniform i_witness) :=
  fun z => fto ((otf z) + e * w).

Lemma order_ge1 : g ^+ succn (succn (Zp_trunc q)) = g ^+ q.
Proof.
  rewrite Zp_cast.
  - reflexivity.
  - apply prime_gt1, prime_order. 
Qed.

Lemma bij_f w e : bijective (f w e).
Proof.
  pose f' := f e w.
  subst f'. unfold f.
  exists (fun x => (fto (otf x - w * e))).
  all: intro x; unfold fto, otf; rewrite !enum_rankK.
  - rewrite GRing.addrK enum_valK. reflexivity. 
  - rewrite GRing.subrK enum_valK. reflexivity. 
Qed.

Lemma schnorr_SHVZK:
  ∀ LA A, 
    ValidPackage LA [interface val #[ RUN ] : chInput → 'option chTranscript] A_export A →
    Advantage SHVZK A = 0.
Proof.
  intros LA A Hvalid. 
  rewrite Advantage_E.
  apply: eq_rel_perf_ind_eq.
  2,3: apply fdisjoints0.
  simplify_eq_rel hwe.
  (* Programming logic part *)
  destruct hwe as [[statement witness] challenge].
  case_eq (R (otf statement) (otf witness)).
  (* We can only simulate if the relation is valid *)
  2: { intros _.
       apply r_ret.
       intuition. }

  (* When relation holds we can reconstruct the first message from the response *)
  unfold R=> rel. apply reflection_nonsense in rel.
  eapply r_uniform_bij with (1 := bij_f (otf witness) (otf challenge))=> z_val.
  apply r_ret.
  (* Ambient logic proof of post condition *)
  intros s0 s1 Hs.
  unfold f.
  rewrite rel.
  split.
  2: apply Hs. 
  simpl.
  rewrite otf_fto expg_mod.
  2: rewrite order_ge1; apply expg_order.
  rewrite expgD - !expgVn.
  rewrite group_prodC group_prodA group_prodC group_prodA /=.
  rewrite expg_mod.
  2 : rewrite order_ge1; apply expg_order.
  rewrite -expgM -expgMn.
  2: apply group_prodC.
  rewrite mulgV expg1n mul1g.
  cbn. rewrite Zp_mulC.
  reflexivity.
Qed.

Lemma hiding_adv :
  ∀ LA A,
    ValidPackage LA [interface val #[ HIDING ] : chInput → 'option chMessage] A_export A →
    aux_hiding A = 0.
Proof.
  intros LA A Va.
  unfold aux_hiding.
  apply: eq_rel_perf_ind_eq.
  2,3 : rewrite ?fset0U; apply fdisjoints0. 
  simplify_eq_rel hwe.
  simplify_linking.
  ssprove_code_simpl.
  destruct hwe as [[h w] e].
  eapply r_uniform_bij.
  1: { assert (bij_f : bijective (fun (e : choiceChallenge) => e)).
       - exists id; done.
       - exact bij_f. }
  move=> e'.
  rewrite !cast_fun_K.
  case_eq (R (otf h) (otf w))=> rel.
  - eapply r_bind with (λ '(b₀, s₀) '(b₁, s₁), match (b₀, b₁) with
                                                 | (Some (a,_,_), Some(a',_,_)) => a' = a
                                                 | _ => false
                                               end ∧ s₀ = s₁ ).
    1: eapply r_bind with (λ '(b₀, s₀) '(b₁, s₁),
                                                  match (b₀, b₁) with
                                                    | (Some (a,_,_), Some(a',_,_)) => a' = a
                                                    | _ => false
                                                  end ∧ s₀ = s₁ ).
    + ssprove_same_head_r=> a.
      apply r_ret.
      move=> ???.
      intuition.
    + move=> a a'.
      eapply r_ret.
      move=> ???.
      destruct a, a'; intuition.
    + move=> a a'.
      apply rpre_hypothesis_rule.
      move=> s0 s1 [Ha Hs].
      destruct a, a'.
      ++ destruct s,s2.
         destruct s,s2.
         rewrite Ha.
         apply r_ret=>?? Hs0. 
         inversion Hs0.
         simpl in H, H0.
         rewrite H H0 Hs.
         split; reflexivity.
      ++ destruct s,s2.
         destruct s,s2.
         exfalso. rewrite - boolp.falseE. assumption.
      ++ exfalso; rewrite - boolp.falseE; assumption.
      ++ exfalso; rewrite - boolp.falseE; assumption.
  - eapply r_bind with (λ '(b₀, s₀) '(b₁, s₁), b₀ =  b₁ /\ s₀ = s₁).
    1: { apply r_ret=>?? ->.
         split; reflexivity. }
    move=> a a'.
    apply rpre_hypothesis_rule=> s0 s1 H.
    inversion H.
    destruct a,a'.
    + destruct s.
      destruct s2.
      destruct s.
      destruct s2.
      apply r_ret=> ?? [Hs1 Hs2].
      inversion H0.
      simpl in Hs1, Hs2.
      rewrite Hs1 Hs2 H1.
      split; reflexivity.
    + inversion H0.
    + inversion H0.
    + apply r_ret=> ?? [Hs1 Hs2].
      simpl in Hs1, Hs2.
      rewrite Hs1 Hs2 H1.
      split; reflexivity.
Qed.

Theorem schnorr_com_hiding :
  ∀ LA A,
    ValidPackage LA [interface val #[ HIDING ] : chInput → 'option chMessage] A_export A →
    AdvantageE (Hiding_real ∘ Sigma_to_Com ∘ SHVZK true) (Hiding_ideal ∘ Sigma_to_Com ∘ SHVZK true) A <= 0.
Proof.
  intros LA A Va.
  have H := commitment_hiding LA A 0 Va.
  rewrite GRing.addr0 in H.
  have HS := schnorr_SHVZK _ _ _.
  rewrite hiding_adv in H.
  rewrite GRing.addr0 in H.
  apply AdvantageE_le_0 in H.
  1: rewrite H; trivial.
  move=> A' Va'.
  have -> := HS LA A' Va'.
  trivial.
Qed.
