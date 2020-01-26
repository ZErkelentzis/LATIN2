

export P="../export/lf-elpi/content/latin..NONE/"

cat "$P\$Proofs.elpi" "$P\$Truth\$N\$D.elpi" "$P\$Alternative\$Negation\$And\$Falsity\$N\$D.elpi" "$P\$Conjunction\$N\$D\$I.elpi" "$P\$Conjunction\$N\$D\$E.elpi" "$P\$Disjunction\$N\$D\$I.elpi" "$P\$Disjunction\$N\$D\$E.elpi" "$P\$Implication\$N\$D\$I.elpi" "$P\$Implication\$N\$D\$E.elpi" | grep -Ev '^accumulate ' > generated/plnd.elpi

cat "$P\$Universal\$Quantification\$N\$D\$I.elpi" "$P\$Universal\$Quantification\$N\$D\$E.elpi" "$P\$Existential\$Quantification\$N\$D\$I.elpi" "$P\$Existential\$Quantification\$N\$D\$E.elpi" | grep -Ev '^accumulate ' > generated/fol.elpi

cat "$P\$Tableaux.elpi" "$P\$Negation\$Tab.elpi" "$P\$Conjunction\$Tab.elpi" "$P\$Disjunction\$Tab.elpi" "$P\$Implication\$Tab.elpi" "$P\$Equivalence\$Tab.elpi" | grep -Ev '^accumulate ' > generated/pltab.elpi
