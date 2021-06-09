
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
  Definition Bool_pos : Positive #|bool_choiceType|.
  Proof.
    rewrite card_bool. done.
  Defined.

  #[local] Existing Instance Bool_pos.

  Definition choiceWitness : chUniverse := 'fin #|Witness|.
  Definition choiceStatement : chUniverse := 'fin #|Statement|.
  Definition choiceMessage : chUniverse := 'fin #|Message|.
  Definition choiceChallenge : chUniverse := 'fin #|Challenge|.
  Definition choiceResponse : chUniverse := 'fin #|Response|.
  Definition choiceTranscript : chUniverse := chProd (chProd choiceMessage choiceChallenge) choiceResponse.
  Definition choiceState := 'fin #|State|.
  Definition choiceBool := 'fin #|bool_choiceType|.

  Definition i_witness := #|Witness|.

  Definition HIDING : nat := 0.
  Definition SOUNDNESS : nat := 1.

  Definition Sigma_locs : {fset Location} := fset0.
  Definition Simulator_locs : {fset Location} := fset0.

  Definition Commit (h : choiceStatement) (w : choiceWitness):
    code Sigma_locs [interface] (choiceMessage × choiceState) :=
    {code
       r ← sample uniform i_witness ;;
       ret (fto (g ^+ otf r), r)
    }.

  Definition Response (h : choiceStatement) (w : choiceWitness) (r : choiceState) (a : choiceMessage) (e : choiceChallenge):
    code Sigma_locs [interface] choiceResponse :=
    {code
       ret (fto (otf r + otf e * otf w))
    }.

  Definition Simulate (h : choiceStatement) (e : choiceChallenge):
    code Simulator_locs [interface] choiceTranscript :=
    {code
       z ← sample uniform i_witness ;;
       ret (fto (g ^+ (otf z) * (otf h ^- (otf e))), e, z)
    }.

  Definition Verify (h : choiceStatement) (a : choiceMessage) (e : choiceChallenge) (z : choiceResponse):
    code Sigma_locs [interface] choiceBool :=
    {code
       ret (fto (g ^+ (otf z) == (otf a) * (otf h) ^+ (otf e)))
    }.

  Definition Extractor (h : choiceStatement) (a : choiceMessage)
                       (e : choiceChallenge) (e' : choiceChallenge)
                       (z : choiceResponse)  (z' : choiceResponse) : 'option choiceWitness :=
    Some (fto ((otf z - otf z') / (otf e - otf e'))).

End MyAlg.


Local Open Scope package_scope.

Module Schnorr := SigmaProtocol MyParam MyAlg.

Import MyParam MyAlg Schnorr.

#[local] Definition f (e w : Witness) :
  Arit (uniform i_witness) → Arit (uniform i_witness) :=
  fun z => fto ((otf z) + e * w).

Lemma order_ge1 : succn (succn (Zp_trunc q)) = q.
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
  - by rewrite addrK enum_valK.
  - by rewrite subrK enum_valK.
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
    ɛ_hiding A = 0.
Proof.
  intros LA A Va.
  unfold ɛ_hiding.
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
    + ssprove_sync_eq=> a.
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
  have -> := HS (LA :|: Sigma_locs) A' Va'.
  trivial.
Qed.

(* Lemma gt_mul_inv : ∀ (g h: gT) x y, (h == g ^+ (x - y) :> gT) = (g ^+y * h == g ^+ x :> gT). *)
(* Proof. *)
(*   intros g h x y. *)
(*   rewrite -expgD. *)
(*   rewrite -subrI. *)
(*   rewrite subrK. *)
(*   rewrite addrAC. *)
(* Qed. *)
(*   rewrite -(inj_eq (@mulgI gT (g^+y))). *)

Lemma extractor_success:
  ∀ LA A LAdv Adv,
    ValidPackage LA [interface val #[ SOUNDNESS ] : chStatement → chBool] A_export A →
    ValidPackage LAdv [interface] [interface val #[ ADV ] : chStatement → chBinding] Adv →
    fdisjoint LA (Sigma_locs :|: LAdv) →
    ɛ_soundness A Adv = 0.
Proof.
  intros LA A LAdv Adv VA VAdv Hdisj.
  apply: eq_rel_perf_ind_eq.
  2,3: apply Hdisj.

  simplify_eq_rel h.
  destruct (Adv ADV).
  1: destruct t, s; repeat destruct (chUniverse_eqP).
  2-4: apply r_ret; auto.
  apply rsame_head=> run.
  rewrite !code_link_scheme.
  destruct run, s0, s0, s1.

  match goal with
      | [ |- context[if ?b then _ else _]] => case b eqn:rel
  end.

  2: apply r_ret; auto.

  apply r_ret.
  intros ?? s_eq.
  split; [| apply s_eq].

  unfold R.
  unfold "&&" in rel.
  inversion rel.

  repeat match goal with
      | [ |- context[if ?b then _ else _]] => case b eqn:?
  end.
  2,3: discriminate.

  rewrite otf_fto in Heqs4.
  rewrite otf_fto in rel.

  apply reflection_nonsense in rel.
  apply reflection_nonsense in Heqs4.

  rewrite H0.
  f_equal.
  rewrite otf_fto.
  rewrite expg_mod.
  2: rewrite order_ge1; apply expg_order.
  rewrite expgM.
  rewrite expg_mod.
  2: rewrite order_ge1; apply expg_order.
  rewrite expgD.
  rewrite -FinRing.zmodVgE.
  rewrite expg_zneg.
  2: apply cycle_id.
  rewrite Heqs4 rel.
  rewrite !expgMn.
  2-3: apply group_prodC.
  rewrite invMg.
  rewrite !expgMn.
  2: apply group_prodC.
  rewrite !group_prodA.
  rewrite group_prodC.
  rewrite group_prodA.
  rewrite group_prodA.
  rewrite -expgMn.
  2: apply group_prodC.
  rewrite mulVg.
  rewrite expg1n mul1g.
  rewrite -expg_zneg.
  2: { have Hx : exists ix, otf h = g ^+ ix.
       { apply /cycleP. rewrite -g_gen. apply: in_setT. }
       destruct Hx as [ix ->].
       apply mem_cycle. }
  rewrite expgAC.
  rewrite [otf h ^+ (- otf s1) ^+ _] expgAC.
  rewrite -expgD.
  rewrite -expgM.
  have <- := @expg_mod _ q.
  2: { have Hx : exists ix, otf h = g ^+ ix.
       { apply /cycleP. rewrite -g_gen. apply: in_setT. }
       destruct Hx as [ix ->].
       rewrite expgAC /q.
       rewrite expg_order.
       apply expg1n. }
  rewrite -modnMmr.
  (* NOTE: *)
  (* Exponent type (subgroup) is Z_q. q is prime. Hence forall x \in Z_q, x < q. *)
  (* Since q is prime all x's are co-prime? *)

  (* FIXME: *)
  (* Currently the inverse element is in Z_q. *)
  (* The element (e - e') is not... *)
  (* The element is treated as a natural number modulo the order of the group. *)
  (* This should be equivalent. *)
  (* Prove this *)
  have -> :
    (modn
       (addn (@nat_of_ord (S (S (Zp_trunc q))) (@otf Challenge s0))
             (@nat_of_ord (S (S (Zp_trunc q)))
                          (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                      (@otf Challenge s1)))) q) =
    (@nat_of_ord (S (S (Zp_trunc q)))
                   (@Zp_add (S (Zp_trunc q)) (@otf Challenge s0) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s1)))).
  { simpl.
    rewrite -> order_ge1 at 2.
    rewrite -> order_ge1 at 3.
    rewrite -> order_ge1 at 4.
    rewrite -> order_ge1 at 5.
    rewrite modnDmr.
    destruct (otf s1) as [a Ha].
    destruct a as [| Pa].
    - simpl.
      rewrite subn0.
      rewrite modnn.
      rewrite addn0.
      rewrite modnDr.
      rewrite -> order_ge1 at 3.
      rewrite modn_small.
      + reflexivity.
      + rewrite <- order_ge1 at 2. apply ltn_ord.
    - simpl.
      rewrite -> order_ge1 at 3.
      rewrite modnDmr.
      reflexivity. }
  have -> :
    (modn
       (muln (@nat_of_ord (S (S (Zp_trunc q)))
                          (@GRing.inv (FinRing.UnitRing.unitRingType (Zp_finUnitRingType (Zp_trunc q)))
                                      (@GRing.add (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                                  (@otf Challenge s0)
                                                  (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                                              (@otf Challenge s1)))))
             (@nat_of_ord (S (S (Zp_trunc q)))
                          (@Zp_add (S (Zp_trunc q)) (@otf Challenge s0) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s1))))) q) =
    (Zp_mul
       (@GRing.inv (FinRing.UnitRing.unitRingType (Zp_finUnitRingType (Zp_trunc q)))
                   (@GRing.add (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                               (@otf Challenge s0)
                               (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q))))
                                           (@otf Challenge s1))))
       (@Zp_add (S (Zp_trunc q)) (@otf Challenge s0) (@Zp_opp (S (Zp_trunc q)) (@otf Challenge s1)))).
  { rewrite -modnMmr.
    simpl.
    rewrite modnDmr.
    rewrite -> order_ge1 at 3.
    rewrite -> order_ge1 at 4.
    rewrite -> order_ge1 at 6.
    rewrite -> order_ge1 at 7.
    rewrite -> order_ge1 at 7.
    rewrite modnMmr.
    reflexivity.
  }
  rewrite Zp_mulVz.
  { cbn. by rewrite eq_refl. }
  rewrite -> order_ge1 at 1.
  set m := (@GRing.add (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q)))) (@otf Challenge s0)
             (@GRing.opp (FinRing.Zmodule.zmodType (Zp_finZmodType (S (Zp_trunc q)))) (@otf Challenge s1))).
  destruct m as [m Hm].
  simpl.
  rewrite order_ge1 in Hm.
Admitted.

Theorem schnorr_com_binding:
  ∀ LA A LAdv Adv,
    ValidPackage LA [interface val #[ SOUNDNESS ] : chStatement → chBool] A_export A →
    ValidPackage LAdv [interface] [interface val #[ ADV ] : chStatement → chBinding] Adv →
    fdisjoint LA (Sigma_locs :|: LAdv) →
    AdvantageE (Com_Binding ∘ Adv) (Special_Soundness_f ∘ Adv) A <= 0.
Proof.
  intros LA A LAdv Adv VA VAdv Hdisj.
  have H := binding LA A LAdv Adv VA VAdv Hdisj.

  rewrite extractor_success in H.
  - apply H.
  - apply Hdisj.
Qed.
