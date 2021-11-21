package latin2.tptp

import info.kwarc.mmt.api.{ContentPath, GlobalName, LocalName, MPath, StructuralElement}
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
import leo.datastructures.TPTP.THF.{FunTyConstructor, FunctionTerm}
import leo.datastructures.TPTP.{AnnotatedFormula, Include, Problem, THF, THFAnnotated}
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.TypedExistentialQuantification.exists
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.SFOLEQ.notequal
import lf.{InternalPropositions, SimpleFunctionTypes}
import lf.SimpleFunctions.{simpapply, simplambda}
import lf.TypedEquality.equal
import lf.TypedUniversalQuantification.forall

import scala.collection.mutable.ArrayBuffer

object HOLExporter {
  def combineStubs(p: GlobalName, ctx: Context, t: Term)(implicit ctrl: Controller): Problem = {
    var includes = ArrayBuffer[MPath]()
    var formulas = ArrayBuffer[AnnotatedFormula]()
    for (x <- ctrl.getTheory(p.module).getDeclarations.takeWhile(_.path != p)) {
      x match
      {
        case PlainInclude(t) => includes += t._1
        case c: Constant => formulas ++= translate_constant(c)
      }
    }
    val axioms = ctx.mapVarDecls {
      case (ctx, vd: VarDecl) =>
        translate_var_decl(vd, ctx)(ctrl)
    }.flatten.distinct

    formulas ++= axioms
    formulas += THFAnnotated("conjecture", "conjecture",  THF.Logical(translate_formula(t)), None)

    val tptp_exporter = ctrl.extman.get(classOf[TPTPExporter]).head

    Problem(includes.map(i => tptp_exporter.translate_include(p.module, i)).toSeq, formulas.toSeq)
  }

  def exportStub(theory: Theory)(implicit ctrl: Controller): Problem = {
    export_theory(theory, Nil)
  }

  def exportTPTP(ctx: Context, what: List[Term])(implicit ctrl: Controller): Problem = {
    // walk through ctx, collect all axioms
    // especially, upon IncludeVarDecls, recurse into referenced theory
    val axioms = ctx.mapVarDecls {
      case (_, vd@IncludeVarDecl(_, _, _)) =>
        val path = vd.tp.get.toMPath
        translate_theory_flattened(ctrl.getTheory(path))
      case (ctx, vd: VarDecl) =>
        translate_var_decl(vd, ctx)(ctrl)
    }.flatten.distinct.map(x => if (x.role == "") { x.copy(role = "axiom") } else x)

    val conjectures = what match {
      case DedList(formulas) => formulas.map(f => THFAnnotated("Conjecture", "conjecture",  THF.Logical(translate_formula(f)), None))
    }

    Problem(List(), (axioms++conjectures))
  }

  def export_theory_flattened(theory: Theory)(implicit ctrl: Controller): Problem = {
    val axioms = translate_theory_flattened(theory).distinct.map(x => if (x.role == "") { x.copy(role = "axiom") } else x)
    Problem(List(), axioms)
  }

  def translate_theory_flattened(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    theory.getIncludesWithoutMeta.flatMap(include => translate_theory_flattened(ctrl.getTheory(include))) ++ theory.getConstants.flatMap(translate_constant)
  }

  def export_theory(theory: Theory, includes: Seq[Include])(implicit ctrl: Controller): Problem = {
    val axioms = translate_theory(theory).map(x => if (x.role == "") { x.copy(role = "axiom") } else x)
    Problem(includes, axioms)
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[THFAnnotated] = {
    theory.getConstants.flatMap(translate_constant)
  }

  def funty_builder(in: List[THF.Formula], out: THF.Formula) = in.foldRight(out)((g, arg) => THF.BinaryFormula(FunTyConstructor, arg, g))

  def translate_decl(name: LocalName, tp: Option[Term], df: Option[Term], ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = tp.map(ctrl.simplifier(_, simplicationUnit))


    newTp match {
      case Some(ded(formula)) =>
        List(THFAnnotated(name.toString, "axiom", THF.Logical(translate_formula(formula)), None))
      case Some(TypeDecl(Nil))  =>
        List(THFAnnotated("type_" + name.toString, "type", THF.Typing("t_" + name.toString, THF.FunctionTerm("$tType", Nil)), None)) //is optional
      case Some(PredDecl(in)) => //TODO: moved this up as -> bool matched on FuncDecl(Nil, OMID(out)) first?
        List(THFAnnotated("type_" + name.toString, "type", THF.Typing("t_" + name.toString, in match {
          case Nil => THF.FunctionTerm("$o", Nil)
          case in => funty_builder(in.map(translate_formula), THF.FunctionTerm("$o", Nil))
        }), None))
      case Some(FuncDecl(Nil, OMID(out))) =>
        List(THFAnnotated("type_" + name.toString, "type", THF.Typing("t_" + name.toString, THF.FunctionTerm("t_" + out.name.toString, Nil)), None))
      case Some(FuncDecl(in, out)) =>
        THFAnnotated("type_" + name.toString, "type", THF.Typing("t_" + name.toString, funty_builder(in.map(translate_formula), translate_formula(out))), None) :: List[THFAnnotated]()//:: (df.map(THFAnnotated("def_" + name.toString, "axiom", THF.QuantifiedFormula(THF.!, ))))
      case _ => Nil
    }
  }

  def translate_var_decl(vd: VarDecl, ctx: Context)(implicit ctrl: Controller): List[THFAnnotated] =
    translate_decl(vd.name, vd.tp, vd.df, ctx)

  def translate_constant(c: Constant)(implicit ctrl: Controller): List[THFAnnotated] =
    translate_decl(c.name, c.tp, c.df, Context(c.path.module))

  def translate_formula(t: Term): THF.Formula = t match {
    case Lambda(v, ty, body) => THF.QuantifiedFormula(THF.^, Seq(("V_" + v.toPath, translate_formula(ty))), translate_formula(body))
    case simplambda(_, _, f) => translate_formula(f)
    case simpapply(_, _, f, x) => translate_formula(ApplySpine(f, x))

    // TODO: ask Navid, Florian said this is needed? YES
    case SimpleFunctionTypes.simpfun(a, b) => funty_builder(List(translate_formula(a)), translate_formula(b))
    case InternalPropositions.bool.term => THF.FunctionTerm("$o", Nil)
    // TODO: product types, etc. still needed

    case forall((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.!,
        Seq(
          ("V_" + v.toPath, translate_formula(ty))
        ),
        translate_formula(body)
      )
    case exists((ty, Lambda(v, _, body))) =>
      THF.QuantifiedFormula(
        THF.?,
        Seq(
          ("V_" + v.toPath, translate_formula(ty))
        ),
        translate_formula(body)
      )
    case forall(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(forall(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    //TODO: add exists like above forall
    case exists(ty, body) =>
      val varname = Context.pickFresh(body.allVars.map(VarDecl(_)), LocalName("x"))._1
      translate_formula(exists(ty, Lambda(varname, ty, ApplySpine(body, OMV(varname)))))
    //TODO: add exists like above forall
    case and(left, right) =>
      THF.BinaryFormula(THF.&, translate_formula(left), translate_formula(right))
    case or(left, right) =>
      THF.BinaryFormula(THF.|, translate_formula(left), translate_formula(right))
    case impl(left, right) =>
      THF.BinaryFormula(THF.Impl, translate_formula(left), translate_formula(right))
    case equiv(left, right) =>
      THF.BinaryFormula(THF.<=>, translate_formula(left), translate_formula(right))
    case equal(ty, left, right) => {
      THF.BinaryFormula(THF.Eq, translate_formula(left), translate_formula(right))
    }
    case notequal(ty, left, right) => {
      THF.BinaryFormula(THF.Neq, translate_formula(left), translate_formula(right))
    }
    case not(arg) =>
      THF.UnaryFormula(THF.~, translate_formula(arg))

    case OMID(f) =>
      THF.FunctionTerm("t_" + f.name.toString, Nil)

    case OMV(x) =>
      THF.FunctionTerm("t_" + x.toString, Nil)

    case ApplySpine(f, args) => args.map(translate_formula).foldLeft(translate_formula(f))((g, arg) => THF.BinaryFormula(THF.App, g, arg))

    case default => println(default)
      ???
  }
}
