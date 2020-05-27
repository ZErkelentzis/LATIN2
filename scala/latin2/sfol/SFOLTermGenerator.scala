package latin2.sfol

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.utils._
import objects._
import modules._
import symbols._
import libraries._
import frontend._
import info.kwarc.mmt.lf._
import lf._
import lf._Option.map

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.util.Random


class SFOLTermGenerator(controller: Controller) {
   import SFOLPatterns._
   def makeTerms(mp: MPath) {
     //toDO: save combination of op symbols, inputs and outputs for further use
     val rnd = new Random()
     val lim = 3
     val theory = new SFOLTheoryAdapter(controller, mp)
     val tps = theory.getTypeSyms
     tps foreach {case (p,_) =>
       println("type symbol " + p.name)
     }
     val funs = theory.getFunSyms

     //generation of variables for terms
     val variables = makeVars(3)
     println("Variables:")
     println(variables)
     var fname = List[GlobalName]()
     val funcs = new HashMapToSet[GlobalName, Term]
     //the hashmap saves the combination [outputtype, (complexity, term)]
     //todo: statt int neue klasse complexity
     //interrasntheit definieren (zb anzahl gleiche sachen auf beinden seiten von istgleich)
     val terms = new HashMapToSet[Term,(Int, Term)] //by florian

     funs.foreach {
       case (p, tp) =>
         println("function symbol " + p.name)
         println("type in LF syntax: " + tp)
         val FuncDecl(ins, out) = tp
         println("inputs: " + ins.mkString(", "))
         println("output: " + out)
         //We save the depth of a term in a hashmap. Combined with the map terms, we now have informations about
         //out type, recursive depth and the term itself available. This should allow us to implement generation
         //limits more easily

         //function name and syntax are saved in a List and a HashMap respectively. This way they can be used
         //continuously in term generation
         fname = p::fname
         funcs += (p, tp)

         //we apply the variables to every distinct input universe to generate the most
         //basic term of each universe, which is a single variable
         //part of initialisation, as those are permanent
         ins.distinct.foreach(t => for (i <- 1 to variables.length) {
           terms += (t, (0, variables.apply(i - 1)))//(t, terdep)
         })
         //println("Terms:")
         //terms.foreach(a => println(a))
     }
     //toDO: possibly problematic: generator generates same term multiple times and gives it back
     //toDo: is that even something to bother about? both checking and not checking will most likely
     //todo: take the same amount of time

     while(true) {
       var trnd = rnd.nextInt()%funcs.toList.length
       var newdepth = 0
       if(trnd < 0){
         trnd *= -1
       }
       val FuncDecl(ins, out) = funcs.getOrEmpty(fname(trnd)).head
       //println("Ins" + ins)
       if(ins.nonEmpty){
         val interms = ins.map(tp =>
           terms(tp).toList
         )
         var args = List[List[Term]]()
         interms.foreach{
           list =>
             var arg = List[Term]()
             list.foreach {
             tup =>
               if(tup._1 < lim){
                 arg = tup._2 :: arg
                 if(tup._1 > newdepth) newdepth = tup._1
               }
             }
             args = arg :: args
         }
         //don't forget to add 1 to newdepth, as so far its only the highest input depth, but new depth is that +1
         newdepth += 1
         //println(args)
         //we fill inputs randomly with exactly the number of required arguments
         val inputs = {
           //first we generate a list with possible arguments for the term
           //I am assuming here that the order of the ins and the order of args are
           //going to be the same. Might turn out to be wrong.
           var m = List[Term]()
           var j = 0
           while(m.length < args.length){
             //println("args: " + args)
             var i = rnd.nextInt()%args(j).length //(k).toList.length
             if(i<0){
               i *= (-1)
             }
             //println("Index: " + i)
             m = args(j)(i) :: m
             j += 1
           }
           m
         }
         //println("Arguments: " + inputs)
         if(inputs.nonEmpty){
           val newterm = ApplySpine(OMS(fname(trnd)), inputs:_*)
           val newtup = (newdepth, newterm)
           terms(out) += newtup
           println("new term: " + newterm.toStr(false))
         }
         //terms.foreach(a => println(a))
         // make a random new term for each function symbol
       }
     }
     //toDO: make Termgenerator object for usage by other objects?
     //toDO: make the generator return a Stream[Term]
   }

  def makeVars(n: Int): List[Term] = {
    //makes n variables
    val v = new mutable.HashSet[Term]
    for(i <- 1 to n){
      val x = OMV("x"+i)
      v += x
    }
    v.toList
  }
}

object SFOLTermGeneratorTest {
  def main(args: Array[String]) {
    val controller = Controller.make(true, true, List("MMT/urtheories", "MMT/LATIN2"))
    controller.handleLine("server on 8080")

    val thyS = "latin:/algebraic?Powers" //algebraic?Commutative
    val thy = Path.parseM(thyS, controller.getNamespaceMap)
    val gen = new SFOLTermGenerator(controller)
    gen.makeTerms(thy)
    //while(true){
      //Thread.sleep(1000)
    //}
  }
}
