package latin2.sfol

import info.kwarc.mmt.api.{GlobalName, Path}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects.OMV
import lf.{Conjunction, Disjunction, Equivalence, Implication, Nat, Negation}

object SFOLTermGeneratorTest {
  def main(args: Array[String]) {
    val controller = Controller.make(true, true, List("MMT/urtheories", "MMT/LATIN2"))
    controller.handleLine("server on 8080")

    val thyS = "latin:/?NatPlusTimes" //algebraic?Commutative algebraic?Powers latin:/?IPLND
    val thy = Path.parseM(thyS, controller.getNamespaceMap)
    val gen = new SFOLTermGenerator(controller, thy)

    //todo: test template a+t+x, make a literal, t term, x variable not sub
    val template = gen.generateTemplate()
    var Tfilterlist = List[GlobalName]()
    var Ffilterlist = List[GlobalName]()
    Tfilterlist = Path.parseS("latin:/?Nat?zero", controller.getNamespaceMap) :: Tfilterlist
    Tfilterlist = Path.parseS("latin:/?Nat?succ", controller.getNamespaceMap) :: Tfilterlist
    //Ffilterlist = Conjunction.and.path :: Ffilterlist
    //Ffilterlist = Disjunction.or.path :: Ffilterlist
    Ffilterlist = Equivalence.equiv.path :: Ffilterlist
    Ffilterlist = Implication.impl.path :: Ffilterlist
    Ffilterlist = Negation.not.path :: Ffilterlist
    val TermCriteria = new GenCriteria(0, 5, 0, Nat.nat.term, 0, 3, false,
      100, 100, 50, false, null, 0, 0, 0, false, Tfilterlist/*, template._1, template._2*/)
    val FormulaCriteria = new GenCriteria(1, 5, 0, null, 0,5, true, 50,
      100, 50,true, TermCriteria, exclude = Ffilterlist)
    //var termstream = gen.TermGenerator()
    //var termstream = gen.TermGenerator(TermCriteria)
    //Nat.nat.term
    var formstream = gen.Generator(FormulaCriteria)

    while(true){
      //println("new term: " + controller.presenter.asString(termstream.head))
      //println("new term: " + termstream.head)
      //termstream = termstream.tail
      println("New Term: " + controller.presenter.asString(formstream.head))
      //println("new formula: " + formstream.head)
      formstream = formstream.tail
    }
    //todo: possible problem with generated code (identifiers) if different capitalization is used in theory
    //level, criteria of generation, integration in applications
  }
}
