Section Modus_tollens.
   Variable S : Set.
   Variable P: S -> Prop.
   Variable Q: S -> Prop.

   Lemma SMt : forall x : S, ~P x -> Q x -> (~Q x -> P x).
   intros x HNotPx HQx HNotQx.
   apply HNotQx in HQx.
   inversion HQx. (* Falsehood implies anything, AKA proof by contradiction *)
   Qed.

End Modus_tollens.
