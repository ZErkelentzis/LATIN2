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
