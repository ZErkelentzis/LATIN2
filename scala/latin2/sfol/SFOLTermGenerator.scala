package latin2.sfol

import info.kwarc.mmt.api._
import objects._
import modules._
import symbols._
import libraries._
import frontend._

import info.kwarc.mmt.lf._

import lf._


class SFOLTermGenerator(controller: Controller) {
   import SFOLPatterns._
   def makeTerms(mp: MPath) {
     val theory = new SFOLTheoryAdapter(controller, mp)
     val funs = theory.getFunSyms
     funs foreach {fs =>
       println("function symbol " + fs.name)
       val tp = fs.tp.getOrElse {println("no type found for " + fs.name); return}
       println("type in LF syntax: " + tp)
       val FuncDecl(ins,out) = tp
       println("inputs: " + ins.mkString(", "))
       println("output: " + out)
     }
   }
}

object SFOLTermGeneratorTest {
  def main(args: Array[String]) {
    val controller = Controller.make(true, true, List("MMT/urtheories", "MMT/LATIN2"))

    val thyS = "latin:/algebraic?Group"
    val thy = Path.parseM(thyS, controller.getNamespaceMap)
    val gen = new SFOLTermGenerator(controller)
    gen.makeTerms(thy)
  }
}
