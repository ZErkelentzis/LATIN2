package latin2.tptp

import info.kwarc.mmt.api.checking.{History, Solver, TypeBasedEqualityRule}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{GeneralError, GlobalName, LocalName, MPath}
import info.kwarc.mmt.lf._
import latin2.tptp.DIHOLExporterUtil._
import latin2.tptp.THFExporterUtil._
import leo.datastructures.TPTP._
import lf._

class DPIHOLExporter extends DIHOLExporter {
  override val priority: Int = 5
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DPIHOL._path

  override def translate_type(t: Term): THF.Formula = t match {
    case TypedPredicateSubtypes.predsub(tp, _) => translate_type(tp)
    case _ => super.translate_type(t)
  }

  override def typing_pred(t:Term, x:Term)(implicit usedVars: List[String]): THF.Formula = {
    t match {
      case TypedPredicateSubtypes.predsub(tp, pred) =>
        THFAnd(THFApp(translate_term(pred), translate_term(x)), typing_pred(tp, x))
      case _ => super.typing_pred(t, x)
    }
  }
}

// Should probably be moved to lf
object ProverBasedPredicateSubtypeEquality extends TypeBasedEqualityRule(Nil, lf.Types.tp.path) {
  /**
   * @param solver provides callbacks to the currently solved system of judgments
   * @param tm1    the first term
   * @param tm2    the second term
   * @param tp     their type
   * @param stack  their context
   * @return true iff the judgment holds; None if the solver should proceed with term-based equality checking
   */
  override def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = (tm1, tm2, tp) match {
    case (TypedPredicateSubtypes.predsub(TypedPredicateSubtypes.predsub(t1, p1), p2), TypedPredicateSubtypes.predsub(t2, q), lf.Types.tp.term) => {
      val conjunctionPreds = Lambda(LocalName("v"), TypedTerms.tm(t1), lf.Conjunction.and(Apply(p1, OMV("v")), Apply(p2, OMV("v"))))
      apply(solver)(TypedPredicateSubtypes.predsub(t1, conjunctionPreds), TypedPredicateSubtypes.predsub(t2, q), lf.Types.tp.term)
    }
    case (TypedPredicateSubtypes.predsub(t1, p), TypedPredicateSubtypes.predsub(TypedPredicateSubtypes.predsub(t2, q1), q2), lf.Types.tp.term) => {
      val conjunctionPreds = Lambda(LocalName("v"), TypedTerms.tm(t2), lf.Conjunction.and(Apply(q1, OMV("v")), Apply(q2, OMV("v"))))
      apply(solver)(TypedPredicateSubtypes.predsub(t1, p), TypedPredicateSubtypes.predsub(t2, conjunctionPreds), lf.Types.tp.term)
    }
    case (TypedPredicateSubtypes.predsub(t1, p), TypedPredicateSubtypes.predsub(t2, q), lf.Types.tp.term) => {
      val j = Equality(stack, t1, t2, Some(lf.Types.tp.term))
      val domainsMatch = solver.check(j)            // this can use the type based equality rule for DHOL

      if (!domainsMatch) return Some(false)
      val predType = DependentFunctionTypes.depfun(t1, Lambda(LocalName("v"), TypedTerms.tm(t1), Booleans.bool))

      val predEqJ = Equality(stack, p, q, Some(predType))
      Some(solver.check(predEqJ))
    }
    case (TypedPredicateSubtypes.predsub(t1, p), t2, lf.Types.tp.term) => {
      val j = Equality(stack, t1, t2, Some(lf.Types.tp.term))
      val domainsMatch = solver.check(j)            // this can use the type based equality rule for DHOL

      if (!domainsMatch) return Some(false)
      val predType = DependentFunctionTypes.depfun(t1, Lambda(LocalName("v"), TypedTerms.tm(t1), Booleans.bool))
      val trivPred = Lambda(LocalName("v"), TypedTerms.tm(t2), Truth._true)

      val predEqJ = Equality(stack, p, trivPred, Some(predType))
      Some(solver.check(predEqJ))
    }
    case (t1, TypedPredicateSubtypes.predsub(t2, q), lf.Types.tp.term) => {
      val j = Equality(stack, t1, t2, Some(lf.Types.tp.term))
      val domainsMatch = solver.check(j)            // this can use the type based equality rule for DHOL

      if (!domainsMatch) return Some(false)
      val predType = DependentFunctionTypes.depfun(t1, Lambda(LocalName("v"), TypedTerms.tm(t1), Booleans.bool))
      val trivPred = Lambda(LocalName("v"), TypedTerms.tm(t1), Truth._true)

      val predEqJ = Equality(stack, trivPred, q, Some(predType))
      Some(solver.check(predEqJ))
    }
    case _ => None
  }

  /**
   * type-based equality reasoning often uses extensionality, which can be inefficient or even lead to cycles.
   * Therefore, these rules are only applied to tm1 = tm2 : tp if tm1 or tm2 satisfies this predicate.
   */
  override def applicableToTerm(solver: Solver, tm: Term): Boolean = true
}
