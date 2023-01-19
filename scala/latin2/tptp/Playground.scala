package latin2.tptp

import info.kwarc.mmt.api.frontend.Extension
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.{LocalName, Path}
import latin2.sfol.CommonSymbols
import lf.Conjunction.and
import lf.Proofs.ded
import lf.Propositions.prop

object Playground extends Extension {
  override def logPrefix: String = "tptp-playground"

  override def start(args: List[String]): Unit = {
    super.start(args)
    controller.handleLine(s"log+ $logPrefix") // this will make calls to log() method actually log to stdout

    log("Hello world from tptp playground!")
    log("Does querying an SFOL constant work here?")
    log("yes, it does: " + controller.getConstant(CommonSymbols.prop.path).toString)

    //OLD TEST:
    val theory = controller.getTheory(Path.parseM("latin:/playground/tptp-exporter?Monoid"))
    // val translated = translate_theory(theory)

    // simulate context for: [F: prop, G: prop, pf: |- F /\ G] ...[BUTTON CLICK]...
    val ctx = Context(
      IncludeVarDecl(theory.path, args = Nil),
      //VarDecl(LocalName("F"), OMS(prop.path)),
      //VarDecl(LocalName("G"), OMS(prop.path)),
      //VarDecl(LocalName("pf"), ded(and(OMV("F"), OMV("G"))))
    )
    //val what = ded(and(OMV("G"), OMV("F")))
    //print(new SFOLExporter().translate_theory(theory)(controller))
    //println(new tptp_exporter.exportTPTP(ctx, Nil)(controller).pretty)
  }
}

