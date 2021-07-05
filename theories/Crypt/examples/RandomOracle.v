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

(* Module Type RandomOracleParams. *)

(*   Parameter Query : finType. *)
(*   Parameter Random : finType. *)

(*   Parameter Query_pos : Positive #|Query|. *)
(*   Parameter Random_pos : Positive #|Random|. *)

(*   #[local] Existing Instance Query_pos.  *)
(*   #[local] Existing Instance Random_pos.  *)

(*   Definition chQuery := 'fin #|Query|. *)
(*   Definition chRandom := 'fin #|Random|. *)

(* End RandomOracleParams. *)

Module Type RO.
  (*      (π : RandomOracleParams). *)
  (* Import π. *)

  Parameter Query : finType.
  Parameter Random : finType.

  Parameter Query_pos : Positive #|Query|.
  Parameter Random_pos : Positive #|Random|.

  #[local] Existing Instance Query_pos.
  #[local] Existing Instance Random_pos.

  Definition chQuery := 'fin #|Query|.
  Definition chRandom := 'fin #|Random|.
  Notation " 'query " := chQuery (in custom pack_type at level 2).
  Notation " 'random " := chRandom (in custom pack_type at level 2).

  Definition i_random := #|Random|.
  Definition QUERY : nat := 0.

  Definition queries_loc : Location := (chMap chQuery chRandom ; 1%N).
  Definition init_loc : Location := ('bool ; 2%N).
  Definition RO_locs : {fset Location} := fset [:: queries_loc ; init_loc].

  Definition Init : code RO_locs [interface] 'unit :=
    {code
       init ← get init_loc ;;
       if init
        then ret Datatypes.tt
        else put queries_loc := emptym ;; put init_loc := true ;; ret Datatypes.tt
    }.

  Definition RO :
    package RO_locs
      [interface]
      [interface val #[ QUERY ] : 'query → 'random] :=
    [package
      def #[ QUERY ] (q : 'query) : 'random
      {
        Init ;;
        queries ← get queries_loc ;;
        match (queries q) with
        | Some r => ret r
        | None   => r ← sample uniform i_random ;;
                    put queries_loc := (setm queries q r) ;;
                    ret r
        end
      }
    ].

End RO.
