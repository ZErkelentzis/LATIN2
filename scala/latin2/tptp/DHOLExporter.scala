package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{GeneralError, GlobalName, LocalName, MPath}
import info.kwarc.mmt.lf._
import latin2.sfol.SFOLPatterns.TypeDecl
import latin2.tptp.DHOLExporterUtil._
import latin2.tptp.DIHOLExporterUtil._
import latin2.tptp.THFExporterUtil._
import leo.datastructures.TPTP._
import lf.TypedEquality.tequal
import lf.TypedExistentialQuantification.texists
import lf.TypedTerms
import lf.TypedUniversalQuantification.tforall

class DHOLExporter extends DIHOLExporter {
  override val priority: Int = 6
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path

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

        def translateTypeDecl(dependentArgs: Context) = {
          val tpDecl = THFAnnotated(type_decl_name(name), "type",
            THF.Typing(translated_type_name(name), THFType), None)
          val translatedArgs = dependentArgs.map(_.tp.get) ::: List(OMS(path), OMS(path))
          val relTp = THFArrow(translatedArgs map translate_type, THFBool)
          val tpRel = THFAnnotated(type_rel_name(name), "type",
            THF.Typing(type_rel_name(name), relTp), None)
          val x = newTypeRelVarName(Some("x"), OMS(path), dependentArgs)
          val xP = primedName(x)
          val translatedBaseType = THFOMS(translated_type_path(path).path)
          val dependentBaseType = ApplyGeneral(OMS(path), dependentArgs.map(_.toTerm))
          val perAxClaimBody = THFUniv(x, translatedBaseType,
            THFUniv(xP, translatedBaseType,
              THFImpl(type_rel(dependentBaseType, THF.Variable(x), THF.Variable(xP)),
                THFEq(THF.Variable(x), THF.Variable(xP)))))
          val perAxClaim = THFQuantifiedAxiom(perAxClaimBody, dependentArgs)
          val perAx = THFAnnotated(tp_per_ax_name(name), "axiom", perAxClaim, None)
          add_formula_comment(name.toString)
          List(tpDecl, tpRel, perAx)
        }
        simplifiedTp match {
          case lf.Types.tp.term | Univ(1) | TypeDecl(Nil) =>
            pathMap ::= (path, translated_type_name(name))
            pathMap ::= (path, translated_type_name(name))
            translateTypeDecl(Context.empty)
          case FunType(args, bdy) if (bdy == Univ(1) || bdy == lf.Types.tp.term) && args.nonEmpty =>
            val dependentArgs = argContext(args)
            pathMap ::= (path, translated_type_name(name))
            pathMap ::= (type_pred_path(path), type_pred_name(name))
            translateTypeDecl(dependentArgs)
          case _ => super.translate_decl(path, tpO, dfO, ctx)
        }
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
    super.translate_var_decl(thy_path, vd, ctx)
  }

  override def translate_term(t: Term): THF.Formula = {
		t match {
		  case Lambda(v, ty, body) =>
		    THF.QuantifiedFormula(THF.^, Seq((translate_var_name(v), translate_type(ty))), translate_term(body))
		  case tforall((ty, Lambda(v, _, body))) =>
		    relativized_forall(v, ty, body)
		  case texists((ty, Lambda(v, _, body))) =>
				val tpCond = typing_pred(ty, OMV(v))
		    THFExist(translate_var_name(v), translate_type(ty), THFAnd(tpCond, translate_term(body)))
		  case tforall(ty, body) =>
		    val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
		    translate_term(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
		  case texists(ty, body) =>
		    val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("X"))._1
		    translate_term(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
      case tequal(tp, s, t) => type_rel(tp, translate_term(s), translate_term(t))
      case _ => super.translate_term(t)
		}
	}

  override def typing_pred(tp:Term, s:Term): THF.Formula = {
    type_rel(tp, translate_term(s), translate_term(s))
  }
  def type_rel(tp:Term, left: THF.Formula, right:THF.Formula): THF.Formula = {
    def relAppl(tp: Term, left: THF.Formula, right:THF.Formula) = tp match {
      case ApplyGeneral(OMS(p), args) =>
        THFAppl(THFTerm(type_rel_name(p.name)), args .map(translate_term(_)) ::: List(left, right))
    }
    // optimized version of typeRel in first-order
    def optimizedRelAppl(tp:Term, left: THF.Formula, right:THF.Formula) = {
      // we might translate relAppl via the reduceAx axiom rather than directly to a PER for base types
      // however brief testing suggests that this doesn't really improve the performance of the overall prover system
      relAppl(tp, left, right)
    }

    def typeRelFuncType(x: String, tp: Term, codomain: Term) = {
      val convertedTp = translate_type(tp)
      val innerEq = type_rel(codomain, THFApp(left, THF.Variable(x)), THFApp(right, THF.Variable(primedName(x))))

      THF.QuantifiedFormula(THF.!, Seq((x, convertedTp), (primedName(x), convertedTp)),
        THF.BinaryFormula(THF.Impl, type_rel(tp, THF.Variable(x), THF.Variable(primedName(x))),
          innerEq))
    }
    tp match {
      case lf.Booleans.bool(()) => THF.BinaryFormula(THF.Eq, left, right)
      case TypedTerms.tm(tp) => type_rel(tp, left, right)
      case base@ApplyGeneral(OMS(_), _) => optimizedRelAppl(base, left, right)
      case FunType((xNameO, xTp)::tl, codomain) =>
        val x = xNameO match {
          case Some(ln) => translate_var_name(ln)
          case None => newTypeRelVarName(None, xTp)(controller)
        }
        typeRelFuncType(x, xTp, FunType(tl, codomain))
      case _ =>
        UNSUPPORTED("Typing relation not defined on unsupported type "+controller.presenter.asString(tp))
    }
  }
}

object DHOLExporterUtil {
  def type_rel_name(name:LocalName) = name.toString + "_rel"
  def tp_per_ax_name(ln: LocalName) = ln.toString+"_per_ax"
  def type_rel_path(path:GlobalName) = path.module ? type_rel_name(path.name)
  def type_rel(path:GlobalName) = THFOMS(type_rel_path(path))
  def newTypeRelVarName(nameO: Option[String], tp: Term, ctx: Context = Context.empty)(implicit controller: Controller) = {
    val preferredName = nameO .getOrElse("x"+controller.presenter.asString(tp))
    val name = Context.pickFresh(ctx, LocalName(preferredName))._1
    translate_var_name(name)
  }

  def primedName(x: String) = x+"_PRIME"
}