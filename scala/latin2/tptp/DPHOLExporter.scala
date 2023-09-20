package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.api.{GeneralError, GlobalName, MPath}
import info.kwarc.mmt.lf.FunType
import latin2.tptp.DHOLExporterUtil.newTypeRelVarName
import leo.datastructures.TPTP._
import lf.{TypedPredicateSubtypes, TypedTerms}
import latin2.tptp.THFExporterUtil._
import latin2.tptp.DIHOLExporterUtil._

class DPHOLExporter extends DHOLExporter {
  override val priority: Int = 7
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
   val name = path.name

   val declTranslated = parseDHOLDeclaration(path, tpO, dfO, ctx, replacer) match {
     case DHOLAbbreviation(path, definien) =>
       definitionSubstituents ::= (path, definien)
       pathMap ::= (path, translated_defn_name(name))
       val defDecl = THFAnnotated(defn_decl_name(name), "definition",
         THF.Logical(translate_term(definien)), None)
       List(defDecl)
     case DHOLTypeDeclaration(ctxTp) =>
       pathMap ::= (path, translated_type_name(name))
       pathMap ::= (type_pred_path(path), type_pred_name(name))
       translateTypeDecl(path, ctxTp)
     case DHOLTermDeclaration(ctxTp, ctxTm, ret) =>
       // ignore the difference to allow using LF Pis instead of depfun
       val ctx = ctxTp ++ ctxTm
       pathMap ::= (path, translated_fun_name(name))
       val funDecl = THFAnnotated(type_decl_name(name), "type",
         THF.Typing(translated_fun_name(name), translate_type(PiOrEmpty(ctx, ret))), None)
       val retPred = typing_pred(PiOrEmpty(ctx, ret), OMS(path))
       lazy val tpAx = THFAnnotated(tp_ax_decl_name(name), "axiom",
         THF.Logical(retPred), None)
       List(funDecl, tpAx)
     case DHOLAxiom(ctxTp, claim) =>
       pathMap ::= (path, ax_decl_name(name))
       val ax_body = translate_term(claim)
       val tax = ctxTp.variables.foldRight(ax_body)((vd, bdy) =>
         THFUniv(translate_var_name(vd.name), translate_type(vd.tp.get), bdy))
       List(THFAnnotated(ax_decl_name(name), "axiom", THF.Logical(tax), None))
   }
   add_formula_comment(name.toString)
   declTranslated
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

  override def type_rel(tp: Term, left: THF.Formula, right: THF.Formula): THF.Formula = {
    tp match {
      case TypedPredicateSubtypes.predsub(tp, pred) =>
        THFAnd(THFAnd(type_rel(tp, left, right),
          THFApp(translate_term(pred), left)), THFApp(translate_term(pred), right))
      case _ => super.type_rel(tp, left, right)
    }
  }
}
