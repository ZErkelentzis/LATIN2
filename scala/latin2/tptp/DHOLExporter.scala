package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.{GlobalName, LocalName}
import info.kwarc.mmt.lf._
import latin2.tptp.DHOLExporterUtil._
import latin2.tptp.THFExporterUtil._
import leo.datastructures.TPTP._
import lf.TypedTerms

class DHOLExporter extends DIHOLExporter {
  override val priority: Int = 6
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path

  override def translateTypeDecl(path: GlobalName, dependentArgs: Context)(implicit ctrl: Controller) : List[THFAnnotated] = {
    val name = path.name
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
    val perAxClaim = if (dependentArgs.nonEmpty) {
      THF.Logical(THF.QuantifiedFormula(THF.!,
        dependentArgs.map({ vd => (translate_var_name(vd.name), translate_type(vd.tp.get())) }), perAxClaimBody))
    } else {
      THF.Logical(perAxClaimBody)
    }
    val perAx = THFAnnotated(tp_per_ax_name(name), "axiom", perAxClaim, None)
    add_formula_comment(name.toString)
    List(tpDecl, tpRel, perAx)
  }

  override def translate_equality(tp: Term, left: Term, right: Term): THF.Formula = type_rel(tp, translate_term(left), translate_term(right))
  override def typing_pred(tp:Term, s:Term): THF.Formula = {
    type_rel(tp, translate_term(s), translate_term(s))
  }
  def type_rel(tp:Term, left: THF.Formula, right:THF.Formula): THF.Formula = {
    def relAppl(tpConstr: GlobalName, tpArgs: List[Term], left: THF.Formula, right:THF.Formula) = {
      THFAppl(THFTerm(type_rel_name(tpConstr.name)), tpArgs .map(translate_term) ::: List(left, right))
    }
    // optimized version of typeRel in first-order
    def optimizedRelAppl(tpConstr: GlobalName, tpArgs: List[Term], left: THF.Formula, right:THF.Formula) = {
      // we might translate relAppl via equality and the relation applied twice to the first argument,
      // rather than directly to a PER for base types
      // however brief testing suggests that this doesn't really improve the performance of the overall prover system
      relAppl(tpConstr, tpArgs, left, right)
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
      case ApplyGeneral(OMS(p), args) => optimizedRelAppl(p, args, left, right)
      case FunType((xNameO, xTp)::tl, codomain) =>
        val x = xNameO match {
          case Some(ln) => translate_var_name(ln)
          case None => newTypeRelVarName(None, xTp)(controller)
        }
        typeRelFuncType(x, xTp, FunType(tl, codomain))
      // type variables, not really supported so we fall back to plain equality
      // TODO: rethink this
      case ApplyGeneral(OMV(_), _) => THF.BinaryFormula(THF.Eq, left, right)
      case _ =>
        UNSUPPORTED("Typing relation not defined on unsupported type "+controller.presenter.asString(tp))
    }
  }
}

object DHOLExporterUtil {
  def type_rel_name(name:LocalName) = name.toString + "_rel"
  def tp_per_ax_name(ln: LocalName) = ln.toString+"_per_ax"
  def type_rel_path(path: GlobalName) = path.module ? type_rel_name(path.name)
  def type_rel(path:GlobalName) = THFOMS(type_rel_path(path))
  def newTypeRelVarName(nameO: Option[String], tp: Term, ctx: Context = Context.empty)(implicit controller: Controller) = {
    val preferredName = nameO .getOrElse("x"+controller.presenter.asString(tp))
    val name = Context.pickFresh(ctx, LocalName(preferredName))._1
    translate_var_name(name)
  }

  def primedName(x: String) = x+"_PRIME"
}