tff(dhol, logic, $$dhol == []).
thf(set, type, set: $tType).
thf(funcAppl, type, funcAppl: !> [A:set]: !> [B:set]: !> [F:set]: !> [X:set]: set).
thf(functionHood, axiom, ! [A:set]: ! [B:set]: ! [F:set]: ! [X:set]: ! [Y:set]: ((X = Y) => ((funcAppl @ A @ B @ F @ X) = (funcAppl @ A @ B @ F @ Y))) ).
thf(functExt, axiom, ! [A:set]: ! [B:set]: ! [F:set]: ! [G:set]: ! [X:set]: (((funcAppl @ A @ B @ F @ X) = (funcAppl @ A @ B @ G @ X)) => (F = G))).
thf(concat, type, concat: !> [A:set]: !> [B:set]: !> [C:set]: !> [F:set]: !> [G:set]: set).
thf(concatAppl, axiom, ! [A:set]: ! [B:set]: ! [C:set]: ! [F:set]: ! [G:set]: ! [X:set]: (funcAppl @ A @ C @ (concat @ A @ B @ C @ F @ G) @ X) = (funcAppl @ B @ C @ F @ (funcAppl @ A @ B @ G @ X)) ).
thf(conj,conjecture, ! [A:set]: ! [B:set]: ! [C:set]: ! [D:set]: ! [F:set]: ! [G:set]: ! [H:set]: ((concat @ A @ C @ D @ F @ (concat @ A @ B @ C @ G @ H)) = (concat @ A @ B @ D @ (concat @ B @ C @ D @ F @ G) @ H))).
