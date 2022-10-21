package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects.Context.{context2list, makeFresh}
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{ContentPath, GeneralError, GlobalName, ImplementationError, LocalName, MPath}
import info.kwarc.mmt.lf._
import latin2.sfol.SFOLPatterns.TypeDecl
import leo.datastructures.TPTP.Comment.{CommentFormat, CommentType}
import leo.datastructures.TPTP.THF.FunTyConstructor
import leo.datastructures.TPTP._
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.SFOLEQ.notequal
import lf.TypedEquality.tequal
import lf.TypedExistentialQuantification.texists
import lf.TypedUniversalQuantification.tforall
import lf.{DependentConjunction, DependentFunctionTypes, DependentFunctions, DependentImplication, Falsity, InternalPropositions, SimpleFunctionTypes, Truth, TypedEquality, TypedTerms}
import info.kwarc.mmt.api
import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, InferenceRule, Solver, TypeBasedEqualityRule}
import info.kwarc.mmt.api.objects.Conversions.localName2OMV
import latin2.tptp.DHOLExporterUtil._
import latin2.tptp.THFExporterUtil._

class DHOLExporter extends DIHOLExporter {
  override val priority: Int = 6
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path

  var predsList: List[(Term, Context)] = Nil
  var theoryPredsList: List[(Term, Context)] = Nil
	private def allPredsList: List[(Term, Context)] = theoryPredsList++predsList

  /**
   *
   * @param path the path of the declaration
   * @param tp the type of the declaration
   * @param df the definien of the declaration
   * @param ctx the context of the declaration
   * @param ctrl the controller
   * @precondition We need to call this method on the declaration in the theory in the order in which they appear in it
   * @return the translation of the declaration
   */
  override def translate_decl(path: GlobalName, tpO: Option[Term], dfO: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    ctx.variables .filter (_.tp.isDefined) .foreach {
      vd => addToPredicatesIfApplicable(vd.toTerm, vd.tp.get, false)
    }
    (tpO, dfO) match {
      case (_, Some(df)) =>
        definitionSubstituents ::= (path, df)
        Nil
      case (Some(tp), None) =>
        val simplicationUnit = SimplificationUnit(Context(path.module), expandConDefs = true, expandVarDefs = true, fullRecursion = true)
        val simplifiedTp = try {
          ctrl.simplifier(tp, simplicationUnit)
        } catch {
          // this shouldn't happen, but it makes more sense to continue anyways, as simplifying is not really necessary
          // TODO: add some error handling
          case e: GeneralError => tp
        }

        val name = path.name

        val declTranslated = simplifiedTp match {
          case TypedTerms.tm(DependentFunctionTypes.depfun(s, t)) => unapplyDepFun(DependentFunctionTypes.depfun(s, t)) match { // declaration of function
            case Some((dependentArgs, ret)) =>
              pathMap ::= (path, translated_fun_name(name))
              if (ret == TypedTerms.tm(InternalPropositions.bool)) {
                theoryPredsList.::=(OMS(path), dependentArgs)
              }
          }
        }
        super.translate_decl(path, tpO, dfO, ctx)
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
  override def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[AnnotatedFormula] = {
    ctx.variables .filter (_.tp.isDefined) .foreach {
      vd => addToPredicatesIfApplicable(vd.toTerm, vd.tp.get, false)
    }
    super.translate_var_decl(thy_path, vd, ctx)
  }

  def addToPredicatesIfApplicable(tm:Term, tp:Term, contextPred: Boolean = true): Unit = {
    val FunType(args, ret) = tp
    if (ret == TypedTerms.tm(InternalPropositions.bool))
			if (contextPred) {		
    		predsList.::=(tm, argContext(args))
        val simplicationUnit = SimplificationUnit(Context.empty, expandConDefs = true, expandVarDefs = true, fullRecursion = true)
        val simplifiedTp = try {
          controller.simplifier(tp, simplicationUnit)
        } catch {
          // this shouldn't happen, but it makes more sense to continue anyways, as simplifying is not really necessary
          // TODO: add some error handling
          case e: GeneralError => tp
        }

        simplifiedTp match {
          case TypedTerms.tm(DependentFunctionTypes.depfun(s, t)) => unapplyDepFun(DependentFunctionTypes.depfun(s, t)) match { // declaration of function
            case Some((dependentArgs, ret)) if dependentArgs.variables.nonEmpty =>
              if (ret == TypedTerms.tm(InternalPropositions.bool)) {
                throw UNSUPPORTED("Cannot quantify over type " + controller.presenter.asString(simplifiedTp) + " in DHOL.")
              }
          }
        }
			} else {	
    		theoryPredsList.::=(tm, argContext(args))
			}
  }

  override def translate_term(t: Term): THF.Formula = {
		predsList = Nil
		t match {
		  case Lambda(v, ty, body) =>
		    addToPredicatesIfApplicable(OMV(translate_var(v)), ty)
		    THF.QuantifiedFormula(THF.^, Seq((translate_var_name(v), translate_type(ty))), translate_term(body))
		  case tforall((ty, Lambda(v, _, body))) =>
		    addToPredicatesIfApplicable(OMV(translate_var(v)), ty)
		    relativized_forall(v, ty, body)
		  case texists((ty, Lambda(v, _, body))) =>
		    addToPredicatesIfApplicable(OMV(translate_var(v)), ty)
				val tpCond = typing_pred(ty, OMV(v))
		    THFExist(translate_var_name(v), translate_type(ty), THFAnd(tpCond, translate_term(body)))
		  case tforall(ty, body) =>
		    val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
		    addToPredicatesIfApplicable(OMV(translate_var(varname)), ty)
		    translate_term(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
		  case texists(ty, body) =>
		    val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
		    addToPredicatesIfApplicable(OMV(translate_var(varname)), ty)
		    translate_term(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
      case _ => super.translate_term(t)
		}
	}

  override def typing_pred(t:Term, x:Term): THF.Formula = {
    t match {
      case lf.Booleans.bool(()) => x match {
        case ApplySpine(OMS(p), args) =>
          def addDisjunct(currentForm: THF.Formula, nextPred: (Term, Context)) = {
            val (pred, argCon) = nextPred
            val appl = translate_term(ApplyGeneral(pred, argCon.map(_.name)))
            val nextDisjunct = argCon.variables.foldRight(appl)({
              case (vd, tm) =>
                val tpCond = typing_pred(vd.tp.get, OMV(vd.name))
                THFExist(vd.name.toString, translate_type(vd.tp.get), THFAnd(tpCond, tm))
            })
            THFOr(currentForm, nextDisjunct)
          }
          allPredsList.foldLeft(THFFalse.asInstanceOf[THF.Formula])(addDisjunct)
        case _ => super.typing_pred(t, x)
      }
      case _ => super.typing_pred(t, x)
    }
  }
}