package latin2.tptp

import info.kwarc.mmt.api._
import checking._
import proving._
import objects._

/**
  * a prover that call an external prover via TPTP
  */
class TPTPProver extends AutomatedProver {
  private def invokeATP(p: Option[CPath],ctx: Context,t: Term): Boolean = {
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

    true
  }

  /** ignores rules and levels, never returns a proof */
  def apply(pu: ProvingUnit,rules: RuleSet,levels: Int): (Boolean,Option[Term]) = {
    val r = invokeATP(pu.component,pu.context,pu.tp)
    (r, None)
  }
}
