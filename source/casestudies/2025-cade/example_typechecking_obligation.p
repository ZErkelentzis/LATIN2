thf(set_type, type, t_set: $tType).
thf(set_rel, type, set_rel: (t_set > (t_set > $o))).
thf(set_per_ax, axiom, (! [V_X:t_set]: ((! [V_X_PRIME:t_set]: ((((set_rel @ V_X) @ V_X_PRIME) => (V_X = V_X_PRIME))))))).

thf(in_type, type, t_in: (t_set > (t_set > $o))).
thf(in_tp_ax, axiom, (! [V_A:t_set,V_A_PRIME:t_set]: ((((set_rel @ V_A) @ V_A_PRIME) => $true
)) )).

%%% thf(elem_type, type, t_elem: $tType).
%%% thf(elem_rel, type, elem_rel: (t_set > (t_elem > (t_elem > $o)))).
%%% elem is a definition and thus inlined

%%% thf(functions_type, type, t_functions: (t_set > (t_set > t_set))).
%%% thf(functions_rel, type, functions_rel, (t_set > (t_set > (t_set > (t_set > $o))))).
%%% the type of functions is defined and thus inlined, although we can additionally create a tptp definition
%%% thf(functions_def, definition, ...).

%%% the definitions of function application and composition are both inlined

thf(conj, conjecture, 
(! [V_s:t_set]: (((set_rel @ V_s) @ V_s) => (! [V_t:t_set]: (((set_rel @ V_t) @ V_t) => (! [V_u:t_set]: (((set_rel @ V_u) @ V_u) =>
(! [V_f :t_set > t_set]: ( (! [V_x:t_set]: (((t_in @ V_x) @ V_s) => ((set_rel @ (V_f @ V_x)) @ (V_f @ V_x))) & (! [V_x:t_set]: (((t_in @ V_x) @ V_s) => ((t_in @ (V_f @ V_x)) @ V_t))) ) =>
(! [V_g:t_set > t_set]: ( ( (! [V_x:t_set]: (((t_in @ V_x) @ V_t) => ((set_rel @ (V_g @ V_x)) @ (V_g @ V_x)))) & (! [V_x:t_set]: (((t_in @ V_x) @ V_t) => ((t_in @ (V_g @ V_x)) @ V_u))) ) =>
(! [V_x:t_set]: (((set_rel @ V_u) @ V_u) => (((t_in @ V_x) @ V_s) => (t_in @ (V_g @ (V_f @ V_x)) @ V_u)))))))))))))
)).
