package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.{GlobalName, LocalName}
import info.kwarc.mmt.lf._
import latin2.tptp.DHOLExporterUtil._
import latin2.tptp.DIHOLExporterUtil.unapplyDepFun
import latin2.tptp.THFExporterUtil._
import leo.datastructures.TPTP._
import lf.TypedTerms

class DHOLExporter extends DIHOLExporter {
  override val priority: Int = 6
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DHOL._path

  override def translateTypeDecl(path: GlobalName, dependentArgs: Context)(implicit ctrl: Controller) : List[THFAnnotated] = {
    implicit var usedVars: List[String] = List.empty
    val name = path.name
    val tpDecl = THFAnnotated(type_decl_name(name), "type",
      THF.Typing(translated_type_name(name), THFType), None)
    val translatedArgs = dependentArgs.map(_.tp.get) ::: List(OMS(path), OMS(path))
    val relTp = THFArrow(translatedArgs map translate_type, THFBool)
    val tpRel = THFAnnotated(type_rel_name(name), "type",
      THF.Typing(type_rel_name(name), relTp), None)
    val (x, vx) = newTypeRelVarName(None, OMS(path), dependentArgs)
    usedVars :+ vx
    val xP = primedName(x)
    val translatedBaseType = THFOMS(translated_type_path(path).path)
    val dependentBaseType = ApplyGeneral(OMS(path), dependentArgs.map(_.toTerm))
    val perAxClaimBody = THFUniv(x, translatedBaseType,
      THFUniv(xP, translatedBaseType,
        THFImpl(type_rel(dependentBaseType, THF.Variable(x), THF.Variable(xP)),
          THFEq(THF.Variable(x), THF.Variable(xP)))))
    val perAxClaim = if (dependentArgs.nonEmpty) {
      THF.Logical(THF.QuantifiedFormula(THF.!,
        dependentArgs.map({ vd => (translate_var_name(vd.name)._1, translate_type(vd.tp.get())) }), perAxClaimBody))
    } else {
      THF.Logical(perAxClaimBody)
    }
    val perAx = THFAnnotated(tp_per_ax_name(name), "axiom", perAxClaim, None)
    add_formula_comment(name.toString)
    List(tpDecl, tpRel, perAx)
  }

  override def translate_equality(tp: Term, left: Term, right: Term)(implicit usedVars: List[String]): THF.Formula = type_rel(tp, translate_term(left), translate_term(right))
  override def typing_pred(tp:Term, s:Term)(implicit usedVars: List[String]): THF.Formula = {
    type_rel(tp, translate_term(s), translate_term(s))
  }
  def type_rel(tp:Term, left: THF.Formula, right:THF.Formula)(implicit usedVars: List[String]): THF.Formula = {
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

    def typeRelFuncType(xn: String, tp: Term, codomain: Term) = {
      val convertedTp = translate_type(tp)
      val xpn = primedName(xn)
      val (x, xp) = (THF.Variable(xn), THF.Variable(xpn))
      val innerEq = type_rel(codomain, THFApp(left, x), THFApp(right, xp))

      THF.QuantifiedFormula(THF.!, Seq((xn, convertedTp), (xpn, convertedTp)),
        THF.BinaryFormula(THF.Impl, type_rel(tp, x, xp),
          innerEq))
    }
    tp match {
      case lf.Booleans.bool(()) => THF.BinaryFormula(THF.Eq, left, right)
      case TypedTerms.tm(tp) => type_rel(tp, left, right)
      case lf.DependentFunctionTypes.depfun(tp, lam) => {
        val (depArgs, bdy) = unapplyDepFun(tp, lam)
        type_rel(Pi(depArgs, bdy), left, right)
      }
      case ApplyGeneral(OMS(p), args) => optimizedRelAppl(p, args, left, right)
      case FunType((xNameO, xTp)::tl, codomain) =>
        val (x, subst): (String, Substitution) = xNameO match {
          case Some(ln) =>
            val name = ln.toString++"_REL"
            val xNew = translate_var_name(LocalName(name))._1
            (xNew, Sub(ln, OMV(name)))
          case None => (newTypeRelVarName(None, xTp)(usedVars, controller)._1, Substitution.empty)
        }
        typeRelFuncType(x, xTp ^ subst, FunType(tl.map({case (nO, tm) => (nO, tm ^ subst)}), codomain ^ subst))
      // type variables, not really supported so we fall back to plain equality
      // TODO: rethink this
      case ApplyGeneral(OMV(_), _) => THF.BinaryFormula(THF.Eq, left, right)
      case _ =>
        UNSUPPORTED("Typing relation not defined on unsupported type "+controller.presenter.asString(tp))
    }
  }
}

object DHOLExporterUtil {
  def type_rel_name(name:LocalName) = add_TPTP_prefix(name.toString + "_rel")
  def tp_per_ax_name(ln: LocalName) = add_TPTP_prefix(ln.toString+"_per_ax")
  def type_rel_path(path: GlobalName) = path.module ? type_rel_name(path.name)
  def type_rel(path:GlobalName) = THFOMS(type_rel_path(path))
  def newTypeRelVarName(nameO: Option[String], tp: Term, ctx: Context = Context.empty)(implicit usedVars: List[String], controller: Controller) = {
    val preferredName = nameO .getOrElse("x_rel"+controller.presenter.asString(tp))
    val name = generate_fresh_var_name_ctx(Some(preferredName))(usedVars, ctx.variables.toList.map(_.name))
    translate_var_name(LocalName(name))
  }

  def primedName(x: String) = x+"_PRIME"
}