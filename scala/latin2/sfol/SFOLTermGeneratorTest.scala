package latin2.sfol

import info.kwarc.mmt.api.{GlobalName, Path}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects.{OMV, Term}
import lf.{Conjunction, Disjunction, Equivalence, Implication, Negation}

object SFOLTermGeneratorTest {
  def main(args: Array[String]) {
    val controller = Controller.make(true, true, List("MMT/urtheories", "MMT/LATIN2"))
    controller.handleLine("server on 8080")

    val thyS = "latin:/?NatPlusTimes" //algebraic?Commutative algebraic?Powers latin:/?NatPlusTimes latin:/?Int
    val thy = Path.parseM(thyS, controller.getNamespaceMap)
    val gen = new SFOLTermGenerator(controller, thy)

    val temp = gen.generatectemp()
    val ctemp = (Conjunction.and.path, 3, 5) :: (Disjunction.or.path, 3, 5) :: List[(GlobalName, Int, Int)]()
    val cnftemp = new TermTemplate(temp._1, temp._2, ctemp)
    val htemp = gen.generateHornTemplate()

    var cnffilter = List[GlobalName]()
    cnffilter = Conjunction.and.path :: cnffilter
    cnffilter = Disjunction.or.path :: cnffilter
    cnffilter = Equivalence.equiv.path :: cnffilter
    cnffilter = Implication.impl.path :: cnffilter
    //val template = gen.generateTemplate()
    //val ctemplate = gen.generatectemp()

    //val varia = new TermTemplate(ctemplate._1, ctemplate._2)
    //val disj = new TermTemplate(null, null, true, Disjunction.or.path, varia, 9, 15)
    //val cnf = new TermTemplate(null, null, true, Conjunction.and.path, disj, 5, 10)

    //val atemp = new TermTemplate(template._1, template._2)

    var typefilter = List[Term]()
    var Tfilterlist = List[GlobalName]()
    var Ffilterlist = List[GlobalName]()
    var Efilterlist = List[GlobalName]()
    //typefilter = Nat.nat.term :: typefilter
    //typefilter = Integer.int.term :: typefilter
    Tfilterlist = Path.parseS("latin:/?Nat?zero", controller.getNamespaceMap) :: Tfilterlist
    Tfilterlist = Path.parseS("latin:/?Nat?succ", controller.getNamespaceMap) :: Tfilterlist
    //Ffilterlist = Conjunction.and.path :: Ffilterlist
    //Ffilterlist = Disjunction.or.path :: Ffilterlist
    //Ffilterlist = Equivalence.equiv.path :: Ffilterlist
    //Ffilterlist = Implication.impl.path :: Ffilterlist
    //Ffilterlist = Negation.not.path :: Ffilterlist
    val TermCriteria = new GenCriteria(false, 5, 3, typefilter, 0, 0,
      false,1, 100, 50, false, null, false,0, 0, 0,
      0, 0, 0, false, Tfilterlist/*, template._1, template._2*/)
    val FormulaCriteria = new GenCriteria(false, 5, 0, typefilter, 0,0,
      false, 50,100, 50,true, TermCriteria, true, 0, 1, 0,
      1,1,0,excludedfunctions = Ffilterlist, logicmode = false)
    val AbsoluteTemplate = new GenCriteria(false, 5, 0, typefilter, 0, 3,
      false,100, 100, 50, false, null,false, 0, 0, 50,
      0, 0, 0,false, Tfilterlist)
    val ContTemplate = new GenCriteria(false, 10, 0, typefilter, 0,1,
      true, 50,100, 50,true, TermCriteria, excludedfunctions = cnffilter,
      temp = cnftemp, logicmode = true)
    val HornTemplate = new GenCriteria(false, 3, 0, typefilter, 0,0,
      true, 50,100, 50,true, TermCriteria, excludedfunctions = Efilterlist,
      temp = htemp, logicmode = false)
    //var termstream = gen.TermGenerator()
    //var termstream = gen.TermGenerator(TermCriteria)
    //Nat.nat.term
    var formstream = gen.Generator(HornTemplate)

    while(true){
      //println("new term: " + controller.presenter.asString(termstream.head))
      //println("new term: " + termstream.head)
      //termstream = termstream.tail "New Term: " +
      println(controller.presenter.asString(formstream.head))
      //println("new formula: " + formstream.head)
      formstream = formstream.tail
    }
    //level, criteria of generation, integration in applications
  }
}
