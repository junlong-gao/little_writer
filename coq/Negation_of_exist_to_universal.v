Section Negation_of_exist_to_universal.

   Variable S : Set.
   Variable P : S -> Prop.

   Lemma NEU : (exists x : S, P x) -> ~(forall x : S, ~P x).
   intro H.
   elim H; intro Hx; intro HPx; clear H.
   intro HForAllx.
   apply HForAllx in HPx.
   exact HPx.
   Qed.

End Negation_of_exist_to_universal.
