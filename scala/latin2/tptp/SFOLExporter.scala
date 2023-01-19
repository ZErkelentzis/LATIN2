package latin2.tptp

import info.kwarc.mmt.api.{GlobalName, LocalName, MPath, StructuralElement}
import info.kwarc.mmt.api.archives.BuildTask
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.presentation.{RenderingHandler, StructurePresenter}
import info.kwarc.mmt.api.symbols.{Constant, Declaration, HasType, PlainInclude}
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.lf.{ApplySpine, Lambda}
import latin2.sfol.CommonSymbols.DedList
import latin2.sfol.SFOLPatterns.{FuncDecl, PredDecl, TypeDecl}
import leo.datastructures.TPTP.Comment.{CommentFormat, CommentType}
import leo.datastructures.TPTP.{AnnotatedFormula, Comment, Include, Problem, TFF, TFFAnnotated}
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.TypedExistentialQuantification.texists
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.TypedEquality.tequal
import lf.TypedUniversalQuantification.tforall

import scala.collection.mutable.ArrayBuffer

class SFOLExporter extends logicExporter {
  val priority: Int = 2
  val theoryPath: info.kwarc.mmt.api.MPath = lf.SFOL._path
  def tptp_conjecture(conj: info.kwarc.mmt.api.objects.Term) = TFFAnnotated("conjecture", "conjecture", TFF.Logical(translate_formula(conj)), None)

  def translate_theory(theory: Theory)(implicit ctrl: Controller) = {
    theory.getConstants.flatMap(translate_constant)
  }

  def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[TFFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandConDefs = true, expandVarDefs = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))

    val name = path.name

    newTp match {
      case Some(ded(formula)) =>
        val nameS = name.toString
        val ret = List(TFFAnnotated(nameS, "axiom", TFF.Logical(translate_formula(formula)), None))
        add_formula_comment(nameS)
        ret
      case Some(TypeDecl(Nil)) =>
        List(TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, TFF.AtomicType("$tType", Nil)), None)) //is optional
      case Some(FuncDecl(Nil, OMID(out))) =>
        List(TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, TFF.AtomicType("t_" + out.name.toString, Nil)), None))
      case Some(FuncDecl(in, out)) =>
        TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, TFF.MappingType(in.map(translate_type), translate_type(out))), None) :: List[TFFAnnotated]() //:: (df.map(TFFAnnotated("def_" + name.toString, "axiom", TFF.QuantifiedFormula(TFF.!, ))))
      case Some(PredDecl(in)) =>
        List(TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, in match {
          case Nil => TFF.AtomicType("$o", Nil)
          case in => TFF.MappingType(in.map(translate_type), TFF.AtomicType("$o", Nil))
        }), None))
      case _ => Nil
    }
  }

  def translate_formula(t: Term): TFF.Formula = t match {
    case tforall((ty, Lambda(v, _, body))) =>
      TFF.QuantifiedFormula(
        TFF.!,
        Seq(
          ("V_" + v.toPath, Some(translate_type(ty)))
        ),
        translate_formula(body)
      )
    case texists((ty, Lambda(v, _, body))) =>
      TFF.QuantifiedFormula(
        TFF.?,
        Seq(
          ("V_" + v.toPath, Some(translate_type(ty)))
        ),
        translate_formula(body)
      )
    case tforall(ty, body) =>
      val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case texists(ty, body) =>
      val varname = Context.pickFresh(body.freeVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(texists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case and(left, right) =>
      TFF.BinaryFormula(TFF.&, translate_formula(left), translate_formula(right))
    case or(left, right) =>
      TFF.BinaryFormula(TFF.|, translate_formula(left), translate_formula(right))
    case impl(left, right) =>
      TFF.BinaryFormula(TFF.Impl, translate_formula(left), translate_formula(right))
    case equiv(left, right) =>
      TFF.BinaryFormula(TFF.<=>, translate_formula(left), translate_formula(right))
    case tequal(ty, left, right) => {
      TFF.Equality(translate_term(left), translate_term(right))
    }
    case not(arg) =>
      TFF.UnaryFormula(TFF.~, translate_formula(arg))

    case OMID(f) =>
      TFF.AtomicFormula("t_" + f.name.toString, Nil)

    case OMV(x) => {
      TFF.AtomicFormula("t_" + x.toString, Nil)
    }

    case ApplySpine(OMID(f), args) =>
      TFF.AtomicFormula("t_" + f.name.toString, args.map(translate_term))

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
      TFF.AtomicFormula("$true", Nil)
  }

  def translate_term(t: Term): TFF.Term = t match {
    case ApplySpine(OMID(f), args) =>
      // f: GlobalName, args: List[Term]
      TFF.AtomicTerm("t_" + f.name.toString, args.map(translate_term))

    case OMID(f) =>
      TFF.AtomicTerm("t_" + f.name.toString, Nil)

    //case OMV(x) =>
    //  // x: LocalName
    //  Var(x.name.toString)
    case OMV(x) =>
      // x: LocalName
      TFF.Variable("V_" + x.toString)

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown term/op: " + default)
      TFF.AtomicTerm("$true", Nil)
  }

  def translate_type(t: Term): TFF.Type = t match {
    case OMID(f) =>
      TFF.AtomicType("t_" + f.name.toString, Nil)

    case default =>
      currentFormulaComments +:= Comment(CommentFormat.LINE, CommentType.NORMAL, "Unknown type: " + default)
      TFF.AtomicType("$type", Nil)
  }
}
