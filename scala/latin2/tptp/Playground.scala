package latin2.tptp

import info.kwarc.mmt.api.frontend.Extension
import latin2.sfol.CommonSymbols

object Playground extends Extension {
  override def logPrefix: String = "tptp-playground"

  override def start(args: List[String]): Unit = {
    super.start(args)
    controller.handleLine(s"log+ $logPrefix") // this will make calls to log() method actually log to stdout

    log("Hello world from tptp playground!")
    log("Does querying an SFOL constant work here?")
    log("yes, it does: " + controller.getConstant(CommonSymbols.prop.path).toString)
  }
}