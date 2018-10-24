Section Drinker_paradox.
   Variable S : Set.
   Variable d : S.  (* S is not empty *)
   Variable P : S -> Prop.

   Hypothesis ExclusionOfMiddle : forall A : Prop, A \/ ~ A.

   Lemma main : exists d : S, P d -> forall d : S, P d.
   elim (ExclusionOfMiddle (exists x : S, ~P x)).
      (* first case, there is x that ~P x *)
      intros (Hx, H_not_Px).
      exists Hx. (* get rid of the exists *)
      intro H_P_x.
      contradiction.

      (* second case, for all x P x *)
      intro H_no_not_P_x.
      (* now we are not stuck here since the predicate
         inside the exist is yet to be shown.*)
      exists d.
      intros H_P_d.
      intros d'.
      (* now we are really stuck. we need to show
         the goal forall x P x is exactly H_no_not_P_x.

         try opening it up with EM on the d'
       *)
      elim (ExclusionOfMiddle (P d')).
         (* case 1 P d' -> P d'*)
         trivial.
         (* case 2 ~P d' -> P d' *)
         intro H_not_P_d'.
         (* now what we know is already False *)
         absurd (exists x : S, ~ P x).
            (* case 1, not absurd *)
            exact H_no_not_P_x.
            (* case 2, use exists d' *)
            exists d'.
            exact H_not_P_d'.
    Qed.
End Drinker_paradox.
