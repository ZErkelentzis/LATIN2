package latin2.sfol

import info.kwarc.mmt.api.Path
import info.kwarc.mmt.api.frontend.Controller

object SFOLTermGeneratorTest {
  def main(args: Array[String]) {
    val controller = Controller.make(true, true, List("MMT/urtheories", "MMT/LATIN2"))
    controller.handleLine("server on 8080")

    val thyS = "latin:/?NatPlus" //algebraic?Commutative algebraic?Powers latin:/?IPLND
    val thy = Path.parseM(thyS, controller.getNamespaceMap)
    val gen = new SFOLTermGenerator(controller, thy, 3)
    var termstream = gen.makeTerms()

    while(true){
      println("new term: " + termstream.head)
      termstream = termstream.tail
    }
  }
}
