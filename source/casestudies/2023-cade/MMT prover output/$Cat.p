thf(obj_type, type, t_obj: $tType).
thf(obj_rel, type, obj_rel: (t_obj > (t_obj > $o))).
thf(obj_per_ax, axiom, (! [V_X:t_obj]: ((! [V_X_PRIME:t_obj]: ((((obj_rel @ V_X) @ V_X_PRIME) => (V_X = V_X_PRIME))))))).
thf(mor_type, type, t_mor: $tType).
thf(mor_rel, type, mor_rel: (t_obj > (t_obj > (t_mor > (t_mor > $o))))).
thf(mor_per_ax, axiom, (! [V_X:t_obj,V_Y:t_obj]: ((! [V_X__R:t_mor]: ((! [V_X__R_PRIME:t_mor]: ((((((mor_rel @ V_X) @ V_Y) @ V_X__R) @ V_X__R_PRIME) => (V_X__R = V_X__R_PRIME))))))))).
thf(id_type, type, t_id: (t_obj > t_mor)).
thf(id_tp_ax, axiom, (! [V_X:t_obj,V_X_PRIME:t_obj]: ((((obj_rel @ V_X) @ V_X_PRIME) => ((((mor_rel @ V_X) @ V_X) @ (t_id @ V_X)) @ (t_id @ V_X)))))).
thf(comp_type, type, t_comp: (t_obj > (t_obj > (t_obj > (t_mor > (t_mor > t_mor)))))).
thf(comp_tp_ax, axiom, (! [V_X:t_obj,V_X_PRIME:t_obj]: ((((obj_rel @ V_X) @ V_X_PRIME) => (! [V_Y:t_obj,V_Y_PRIME:t_obj]: ((((obj_rel @ V_Y) @ V_Y_PRIME) => (! [V_Z:t_obj,V_Z_PRIME:t_obj]: ((((obj_rel @ V_Z) @ V_Z_PRIME) => (! [V_F:t_mor,V_F_PRIME:t_mor]: ((((((mor_rel @ V_X) @ V_Y) @ V_F) @ V_F_PRIME) => (! [V_G:t_mor,V_G_PRIME:t_mor]: ((((((mor_rel @ V_Y) @ V_Z) @ V_G) @ V_G_PRIME) => ((((mor_rel @ V_X) @ V_Z) @ (((((t_comp @ V_X) @ V_Y) @ V_Z) @ V_F) @ V_G)) @ (((((t_comp @ V_X) @ V_Y) @ V_Z) @ V_F) @ V_G)))))))))))))))))).
thf(ax1_ax, axiom, (! [V_X:t_obj]: ((((obj_rel @ V_X) @ V_X) => (! [V_Y:t_obj]: ((((obj_rel @ V_Y) @ V_Y) => (! [V_M:t_mor]: ((((((mor_rel @ V_X) @ V_Y) @ V_M) @ V_M) => ((((mor_rel @ V_X) @ V_Y) @ t_comp(V_X,V_Y,V_Y,V_M,t_id(V_Y))) @ V_M))))))))))).
thf(ax2_ax, axiom, (! [V_X:t_obj]: ((((obj_rel @ V_X) @ V_X) => (! [V_Y:t_obj]: ((((obj_rel @ V_Y) @ V_Y) => (! [V_M:t_mor]: ((((((mor_rel @ V_X) @ V_Y) @ V_M) @ V_M) => ((((mor_rel @ V_X) @ V_Y) @ t_comp(V_X,V_X,V_Y,t_id(V_X),V_M)) @ V_M))))))))))).
thf(conjecture, conjecture, (! [V_X:t_obj]: ((((obj_rel @ V_X) @ V_X) => (! [V_Y:t_obj]: ((((obj_rel @ V_Y) @ V_Y) => (((obj_rel @ V_X) @ V_Y) => ((((mor_rel @ V_X) @ V_X) @ t_id(V_X)) @ t_id(V_Y)))))))))).