package latin2.tptp

import info.kwarc.mmt.api.StructuralElement
import info.kwarc.mmt.api.archives.BuildTask
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.presentation.{RenderingHandler, StructurePresenter}
import info.kwarc.mmt.api.symbols.Constant
import info.kwarc.mmt.api.uom.SimplificationUnit
import info.kwarc.mmt.lf.{ApplySpine, Lambda}
import latin2.sfol.CommonSymbols.DedList
import latin2.sfol.SFOLPatterns.{AxDecl, FuncDecl, PredDecl, TypeDecl}
import leo.datastructures.TPTP.{Problem, TFF, TFFAnnotated, Include}
import lf.Conjunction.and
import lf.Disjunction.or
import lf.Equivalence.equiv
import lf.TypedExistentialQuantification.exists
import lf.Implication.impl
import lf.Negation.not
import lf.Proofs.ded
import lf.Types.tp
import lf.TypedEquality.equal
import lf.TypedUniversalQuantification.forall

class SFOLExporter extends StructurePresenter { //TODO: Extension in exporter
  override def apply(e : StructuralElement, standalone: Boolean = false)(implicit rh : RenderingHandler): Unit = {}

  /** a string identifying this build target, used for parsing commands, logging, error messages */
  override def key: _root_.scala.Predef.String = "tptp"

  override def exportTheory(thy : Theory, bf: BuildTask): Unit = {
    outputTo(getOutFileForModule(thy.path).get) {
      //TODO: Theory name sanitizing
      rh(export_theory(thy)(controller).pretty)
    }
  }

  def exportTPTP(ctx: Context, what: List[Term])(implicit ctrl: Controller): Problem = {
    // walk through ctx, collect all axioms
    // especially, upon IncludeVarDecls, recurse into referenced theory
    val axioms = ctx.mapVarDecls {
      case (_, vd@IncludeVarDecl(_, _, _)) =>
        val path = vd.tp.get.toMPath
        translate_theory(ctrl.getTheory(path))
      case (ctx, vd: VarDecl) =>
        translate_var_decl(vd, ctx)(ctrl).toList
    }.flatten.distinct.map(x => if (x.role == "") { x.copy(role = "axiom") } else x)

    val conjectures = what match {
      case DedList(formulas) => formulas.map(f => TFFAnnotated("Conjecture", "conjecture",  TFF.Logical(translate_formula(f)), None))
    }

    Problem(List(), (axioms++conjectures))
  }

  def export_theory(theory: Theory)(implicit ctrl: Controller): Problem = {
    val includes = theory.getIncludesWithoutMeta.map(in => ("$" + in.name.toString + ".tptp", Nil)) //TODO: should be .ax
    val axioms = translate_theory(theory).map(x => if (x.role == "") { x.copy(role = "axiom") } else x)

    Problem(includes, axioms)
  }

  def translate_theory(theory: Theory)(implicit ctrl: Controller): List[TFFAnnotated] = {
    theory.getIncludesWithoutMeta.flatMap(include => translate_theory(ctrl.getTheory(include))) ++ theory.getConstants.flatMap(translate_constant)
  }

  def translate_var_decl(vd: VarDecl, ctx: Context)(implicit ctrl: Controller): Option[TFFAnnotated] = {
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = vd.tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) =>
        Some(TFFAnnotated(vd.name.toString, "", TFF.Logical(translate_formula(formula)), None))
      case _ => None
    }
  }

  //TODO: difference Constant, VarDecl?

  def translate_constant(c: Constant)(implicit ctrl: Controller): Option[TFFAnnotated] = {
    val ctx = Context(c.path.module)
    val simplicationUnit = SimplificationUnit(ctx, expandDefinitions = true, fullRecursion = true)

    val newTp = c.tp.map(ctrl.simplifier(_, simplicationUnit))

    newTp match {
      case Some(ded(formula)) => //TODO: difference to AxDecl?
        Some(TFFAnnotated(c.name.toString, "", TFF.Logical(translate_formula(formula)), None))
      case Some(TypeDecl(Nil)) =>
        Some(TFFAnnotated(c.name.toString+"_type", "type", TFF.Typing(c.name.toString, TFF.AtomicType("$tType", Nil)), None)) //is optional
      case Some(FuncDecl(Nil, OMID(out))) =>
        Some(TFFAnnotated(c.name.toString+"_type", "type", TFF.Typing(c.name.toString, TFF.AtomicType(out.name.toString, Nil)), None))
      case Some(FuncDecl(in, out)) =>
        Some(TFFAnnotated(c.name.toString+"_type", "type", TFF.Typing(c.name.toString, TFF.MappingType(in.map(translate_type), translate_type(out))), None))
      case Some(PredDecl(in)) =>
        Some(TFFAnnotated(c.name.toString+"_type", "type", TFF.Typing(c.name.toString, TFF.MappingType(in.map(translate_type), TFF.AtomicType("$o", Nil))), None))
      case _ => None
    }
  }

  def translate_formula(t: Term): TFF.Formula = t match {
    case forall((ty, Lambda(v, _, body))) =>
      TFF.QuantifiedFormula(
        TFF.!,
        Seq(
          (v.toPath, Some(translate_type(ty)))
        ),
        translate_formula(body)
      )
    case exists((ty, Lambda(v, _, body))) =>
      TFF.QuantifiedFormula(
        TFF.?,
        Seq(
          (v.toPath, Some(translate_type(ty)))
        ),
        translate_formula(body)
      )

    case and(left, right) =>
      TFF.BinaryFormula(TFF.&, translate_formula(left), translate_formula(right))
    case or(left, right) =>
      TFF.BinaryFormula(TFF.|, translate_formula(left), translate_formula(right))
    case impl(left, right) =>
      TFF.BinaryFormula(TFF.Impl, translate_formula(left), translate_formula(right))
    case equiv(left, right) =>
      TFF.BinaryFormula(TFF.<=>, translate_formula(left), translate_formula(right))
    case equal(ty, left, right) => {
      TFF.Equality(translate_term(left), translate_term(right))
    }
    case not(arg) =>
      TFF.UnaryFormula(TFF.~, translate_formula(arg))

    case OMID(f) =>
      TFF.AtomicFormula(f.name.toString, Nil)

    case OMV(x) =>
      TFF.AtomicFormula(x.toString, Nil)

    case ApplySpine(OMID(f), args) =>
      TFF.AtomicFormula(f.name.toString, args.map(translate_term))

  }

  def translate_term(t: Term): TFF.Term = t match {
    case ApplySpine(OMID(f), args) =>
      // f: GlobalName, args: List[Term]
      TFF.AtomicTerm(f.name.toString, args.map(translate_term))

    case OMID(f) =>
      TFF.AtomicTerm(f.name.toString, Nil)

    //case OMV(x) =>
    //  // x: LocalName
    //  Var(x.name.toString)
    case OMV(x) =>
      // x: LocalName
      TFF.Variable(x.toString)
  }

  def translate_type(t: Term): TFF.Type = t match {
    case OMID(f) =>
      TFF.AtomicType(f.name.toString, Nil)
  }
}
