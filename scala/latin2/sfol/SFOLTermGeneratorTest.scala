package latin2.sfol

import info.kwarc.mmt.api.Path
import info.kwarc.mmt.api.frontend.Controller
import lf.Nat

object SFOLTermGeneratorTest {
  def main(args: Array[String]) {
    val controller = Controller.make(true, true, List("MMT/urtheories", "MMT/LATIN2"))
    controller.handleLine("server on 8080")

    val thyS = "latin:/?NatPlus" //algebraic?Commutative algebraic?Powers latin:/?IPLND
    val thy = Path.parseM(thyS, controller.getNamespaceMap)
    val gen = new SFOLTermGenerator(controller, thy, 4)
    val TermCriteria = new GenCriteria(1, Nat.nat.term, 0, 3, 90)
    val FormulaCriteria = new GenCriteria(1, null, 0, 3, 50, true,
      TermCriteria)
    //var termstream = gen.TermGenerator()
    //var termstream = gen.TermGenerator(TermCriteria)
    //Nat.nat.term
    var formstream = gen.FormulaGenerator(FormulaCriteria)

    while(true){
      //println("new term: " + controller.presenter.asString(termstream.head))
      //println("new term: " + termstream.head)
      //termstream = termstream.tail
      println("new formula: " + controller.presenter.asString(formstream.head))
      //println("new formula: " + formstream.head)
      formstream = formstream.tail
    }
    //todo: possible problem with generated code (identifiers) if different capitalization is used in theory
    //level, criteria of generation, integration in applications
  }
}
