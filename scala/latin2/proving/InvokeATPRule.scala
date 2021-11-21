package latin2.proving

import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, Solver}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.parser.ParseResult
import info.kwarc.mmt.api.{GlobalName, Path}
import info.kwarc.mmt.lf.OfType
import latin2.tptp.{SFOLExporter, TPTPExporter}
import lf.Proofs

import scala.annotation.tailrec
import scala.sys.process.Process

object InvokeATPRule extends InferenceAndTypingRule(Path.parseS("latin:/?PropositionsATP?atp_proof"), OfType.path) {

  private def invokeATP(p: GlobalName, ctx: Context, t: Term)(implicit  ctrl: Controller): Boolean = {
    val tptp_exporter = ctrl.extman.get(classOf[TPTPExporter]).head;
    val problem = tptp_exporter.combineStubs(p, ctx, t)

    // TODO (XBagon): step 0: outsource this method to the tptp folder
    // TODO(XBagon): step 1:
    //    ctrl.getTheory(p.module).getDeclarations.dropUntil(_.path == p).map {
    //       case PlainInclude(...) => synthesize TPTP include
    //       case c: Constant if c.tp.contains(|- F) for some F => synthesize TPTP axiom for F
    //    }
    //    synthesize TPTP axioms for all vardecls `vd: |- F` in ctx
    //    synthesize TPTP conjecture for t
    //    print synthesized TPTP things to a file (and inspect that manually)
    //    and return true (for now)
    //
    // TODO(XBagon): step 2: call external ATP instead of returning true

    // to see examples what this prints, either run or see comments in tptp-exporter_monoid.mmt.
    println(s"invoked ATP on `$t` in context `$ctx` for constant `$p`")

    problem.map(tptp_exporter.exportProblem(_, p.module)).map(callExternalATP).isDefined
  }

  def callExternalATP(path: String)(implicit  ctrl: Controller) = {
    println(s"""java -jar ${sys.env("LEO3")} $path """)
    val pb = Process(s"""java -jar ${sys.env("LEO3")} $path """)
    val result = pb.!!
    println(result)
  }

  @tailrec
  override def applicable(t: Term): Boolean = t match {
    case OMA(OMS(`head`), _) => true
    // applicable under unknowns introduced by parsing/solver
    case OMBINDC(OMS(ParseResult.unknown), _, List(t)) => applicable(t)
    case _ => false
  }

  override def apply(solver: Solver, tm: Term, tp: Option[Term], covered: Boolean)(implicit stack:  Stack, history: History): (Option[Term], Option[Boolean]) = tm match {
    case OMA(OMS(`head`), List(formula)) =>
      tp.foreach(givenTp => {
        if (!solver(Equality(stack, Proofs.ded(formula), givenTp, None))) {
          solver.error("???")
          return (None, Some(false))
        }
      })

      val outerConstant = solver.checkingUnit.component.map(_.parent).collect {
        case p: GlobalName => p
      }.getOrElse {
        solver.error("cannot identify constant in which ATP call happened")
        return (None, None)
      }

      val formulaProvable = invokeATP(outerConstant, stack.context, formula)(solver.controller)

      if (formulaProvable) {
        (Some(Proofs.ded(formula)), Some(true))
      } else {
        // TODO: say which ATP was chosen, say why it did fail
        //       (did it report "unprovable" or did it fail unexpectedly?)
        solver.error(s"External ATP failed proving `$formula`.")
        (None, Some(false))
      }

    case _ => (None, None)
  }
}
