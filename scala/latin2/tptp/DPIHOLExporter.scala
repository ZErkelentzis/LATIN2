package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.Context.{context2list, makeFresh}
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{GeneralError, GlobalName, LocalName, MPath}
import info.kwarc.mmt.lf._
import leo.datastructures.TPTP._
import lf.{Booleans, DependentFunctionTypes, Truth, TypedPredicateSubtypes, TypedTerms}
import info.kwarc.mmt.api.checking.{History, Solver, TypeBasedEqualityRule}
import latin2.tptp.THFExporterUtil._
import latin2.tptp.DHOLExporterUtil._

class DPHOLExporter extends DHOLExporter {
  override val priority: Int = 5
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DPHOL._path

  /**
   *
   * @param path the path of the declaration
   * @param tpO the type of the declaration
   * @param dfO the definien of the declaration
   * @param ctx the context of the declaration
   * @param ctrl the controller
   * @precondition We need to call this method on the declaration in the theory in the order in which they appear in it
   * @return the translation of the declaration
   */
 override def translate_decl(path: GlobalName, tpO: Option[Term], dfO: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val Some(tp) = tpO
    val simplicationUnit = SimplificationUnit(Context(path.module), expandConDefs = true, expandVarDefs = true, fullRecursion = true)
    val simplifiedTp = try {
      ctrl.simplifier(tp, simplicationUnit)
    } catch {
      // this shouldn't happen, but it makes more sense to continue anyways, as simplifying is not really necessary
      // TODO: add some error handling
      case e: GeneralError => tp
    }

    val name = path.name

    simplifiedTp match {
      case TypedTerms.tm(predSub@TypedPredicateSubtypes.predsub(tp, pred)) =>
        pathMap ::= (path, translated_fun_name(name))
        val funDecl = THFAnnotated(type_decl_name(name), "type",
          THF.Typing(translated_fun_name(name), translate_type(tp)), None)
        val retPred = typing_pred(predSub, OMS(path))
        lazy val tpAx = THFAnnotated(tp_ax_decl_name(name), "axiom",
          THF.Logical(retPred), None)
        add_formula_comment(name.toString)
        List(funDecl, tpAx)
      case _ => super.translate_decl(path, tpO, dfO, ctx)
    }
  }

  /**
   * translate a context element (variable or assumption) by translating variable types, relativizing them and translating assumptions
   * @param thy_path
   * @param vd the variable declaration to translate
   * @param ctx the context so far
   * @param ctrl the controller
   * @return
   */
  override def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula] = vd match {
    case VarDecl(v, None, Some(TypedTerms.tm(pst@TypedPredicateSubtypes.predsub(tp, _))), _, _) =>
      val funDecl = THFAnnotated(type_decl_name(v), "type",
        THF.Typing(translate_var_name(v), translate_type(tp)), None)
      val retPred = typing_pred(pst, OMS(thy_path ? translate_var_name(v)))
      lazy val tpAx = THFAnnotated(tp_ax_decl_name(v), "axiom",
        THF.Logical(retPred), None)
      List(funDecl, tpAx)
    case _ => super.translate_var_decl(thy_path, vd, ctx)
  }

  override def translate_type(t: Term): THF.Formula = t match {
    case TypedPredicateSubtypes.predsub(tp, _) => translate_type(tp)
    case _ => super.translate_type(t)
  }

  override def typing_pred(t:Term, x:Term): THF.Formula = {
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
