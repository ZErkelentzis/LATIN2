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
import latin2.tptp.CommonExporter.splitFormulasAndComments
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

object SFOLExporter {
  def combineStubs(p: MPath, ctx: Context, t: Term)(implicit ctrl: Controller): Problem = {
    var includes = ArrayBuffer[MPath]()
    var formulasAndComments = ArrayBuffer[(AnnotatedFormula, Option[Comment])]()

    val decls = ctrl.getTheory(p).getDeclarations
    //for (x <- ctrl.getTheory(p.module).getDeclarations.takeWhile(x => x.parent == p)) {
    for (x <- decls.take(decls.length - 1)) {
      x match
      {
        case PlainInclude(t) => includes :+= t._1
        case c: Constant => formulasAndComments ++= translate_constant(c)
      }
    }
    val axioms = ctx.mapVarDecls {
      case (ctx, vd: VarDecl) =>
        translate_var_decl(p.module, vd, ctx)(ctrl)
    }.flatten.distinct

    formulasAndComments ++= axioms

    val ded(conjecture) = t
    formulasAndComments :+= (TFFAnnotated("conjecture", "conjecture",  TFF.Logical(translate_formula(conjecture)), None), None)

    val tptp_exporter = ctrl.extman.get(classOf[TPTPExporter]).head

    val (formulas, comments) = splitFormulasAndComments(formulasAndComments.toList)

    Problem(includes.map(i => tptp_exporter.translate_include(p.module, i)).toSeq, formulas, comments)
  }

  def exportStub(theory: Theory)(implicit ctrl: Controller): Problem = {
    export_theory(theory, Nil)
  }

  def export_theory(theory: Theory, includes: Seq[Include])(implicit ctrl: Controller): Problem = {
    val axioms = translate_theory(theory).map(x => if (x._1.role == "") { x.copy(_1 = x._1.copy(role = "axiom")) } else x)
    val (formulas, comments) = splitFormulasAndComments(axioms)
    Problem(includes, formulas, comments)
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[(TFFAnnotated, Option[Comment])] = {
    theory.getConstants.flatMap(translate_constant)
  }

  def translate_decl(path: GlobalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[(TFFAnnotated, Option[Comment])] = {
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))

    val name = path.name

    newTp match {
      case Some(ded(formula)) =>
        List((TFFAnnotated(name.toString, "axiom", TFF.Logical(translate_formula(formula)), None), None))
      case Some(TypeDecl(Nil))  =>
        List((TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, TFF.AtomicType("$tType", Nil)), None), None)) //is optional
      case Some(FuncDecl(Nil, OMID(out))) =>
        List((TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, TFF.AtomicType("t_" + out.name.toString, Nil)), None), None))
      case Some(FuncDecl(in, out)) =>
        (TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, TFF.MappingType(in.map(translate_type), translate_type(out))), None), None) :: List[(TFFAnnotated, Option[Comment])]()//:: (df.map(TFFAnnotated("def_" + name.toString, "axiom", TFF.QuantifiedFormula(TFF.!, ))))
      case Some(PredDecl(in)) =>
        List((TFFAnnotated("type_" + name.toString, "type", TFF.Typing("t_" + name.toString, in match {
          case Nil => TFF.AtomicType("$o", Nil)
          case in => TFF.MappingType(in.map(translate_type), TFF.AtomicType("$o", Nil))
        }), None), None))
      case _ => Nil
    }
  }

  def translate_var_decl(thy_path: MPath, vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[(TFFAnnotated, Option[Comment])] =
    translate_decl(thy_path ? vd.name, vd.tp, vd.df, ctx)

  def translate_constant(c: Constant)(implicit ctrl: Controller): List[(TFFAnnotated, Option[Comment])] =
    translate_decl(c.path, c.tp, c.df, Context(c.path.module))

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
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(tforall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    case texists(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
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
  }

  def translate_type(t: Term): TFF.Type = t match {
    case OMID(f) =>
      TFF.AtomicType("t_" + f.name.toString, Nil)
  }
}
