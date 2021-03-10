package proving

import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, Solver, TypingRule}
import info.kwarc.mmt.api.objects.{Stack, Term}
import info.kwarc.mmt.lf.OfType
import lf.PropositionsITP
/*
object TacticsAlt extends TypingRule(TacticsAlt.proofAlt.path, OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val PropositionsITP.proof(steps) = tm
  }
}

*/
