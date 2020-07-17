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
//import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.util.Random
//import latin2.sfol.Complexity


class SFOLTermGenerator(controller: Controller, mp: MPath, limit: Int) {
  import SFOLPatterns._
  //todo: should the generator make a°a functions? Are those interesting? How to weed those out?
  val rnd = new Random()
  val lim = limit
  val theory = new SFOLTheoryAdapter(controller, mp)

  val tps = theory.getTypeSyms
  //tps foreach {case (p,_) =>
  //  println("type symbol " + p.name)
  //}
  val funs = theory.getFunSyms

  //generation of variables for terms
  val variables = makeVars(3)
  //println("Variables:")
  //println(variables)
  var fname = List[GlobalName]()
  val funcs = new HashMapToSet[GlobalName, Term]
  //define interestingness further for complexity
  //eg number of equal symbols/variables on both sides of a symbol
  val terms = new HashMapToSet[Term,(Complexity, Term)]

  funs.foreach {
    case (p, tp) =>
      println("function symbol " + p.name)
      println("type in LF syntax: " + tp)
      val FuncDecl(ins, out) = tp
      println("inputs: " + ins.mkString(", "))
      println("output: " + out)

      //function name and syntax are saved in a List and a HashMap respectively. This way they can be used
      //continuously in term generation
      fname = p::fname
      funcs += (p, tp)

      //we apply the variables to every distinct input universe to generate the most
      //basic term of each universe, which is a single variable
      //part of initialisation, as those are permanent
      ins.distinct.foreach(t => for (i <- 1 to variables.length) {
        val c = new Complexity(0, List[Term](t), List[GlobalName]())
        terms += (t, (c, variables.apply(i - 1)))//(t, terdep)
      })
    //println("Terms:")
    //terms.foreach(a => println(a))
  }

  //two makeTerms functions - one creates a stream of terms, the other a stream of (complexity, term) tuples
  //todo: type specific term generation, formula generation

  def makeTerms(): Stream[Term] = {
    newTerm()._2 #:: makeTerms()
  }

  def makeTermsInfo(): Stream[(Complexity, Term)] = {
    newTerm() #:: makeTermsInfo()
  }

  def newTerm(): (Complexity, Term) = {
    if(funcs.isEmpty){
      println("There are no functions to generate terms with.")
      //todo: exit program?
    }
    var newdepth = 0
    //using Hashsets for generation of variable and symbol list for new complexity, to avoid duplicates
    var newvar = mutable.HashSet[Term]()
    var newsym = mutable.HashSet[GlobalName]()
    var trnd = rnd.nextInt()%funcs.toList.length
    if(trnd < 0){
      trnd *= -1
    }
    var empty = emptyCheck(trnd)

    //todo: delete special case, funcs without input are ok

    while(empty){
      trnd = rnd.nextInt()%funcs.toList.length
      if(trnd < 0){
        trnd *= -1
      }
      empty = emptyCheck(trnd)
    }
    val FuncDecl(ins, out) = funcs.getOrEmpty(fname(trnd)).head

    //println("Ins" + ins)
    val interms = ins.map(tp =>
      terms(tp).toList
    )
    val args = interms.map{
      list =>
        var arg = List[Term]()
        list.foreach {
          tup =>
            if(tup._1.depth < lim){
              arg = tup._2 :: arg
              for(v <- tup._1.variables){
                newvar+=v
              }
              for(s <- tup._1.symbols){
                newsym+=s
              }
              if(tup._1.depth > newdepth) newdepth = tup._1.depth
            }
        }
        arg
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
    //todo: add a loop with condition that checks the specified/wanted type in case type specific terms are requested
    val newterm = ApplyGeneral(OMS(fname(trnd)), inputs)
    val newcom = new Complexity(newdepth, newvar.toList, newsym.toList)
    val newtup = (newcom, newterm)
    terms(out) += newtup
    //println("new term: " + newterm.toStr(false))
    //terms.foreach(a => println(a))
    // make a random new term for each function symbol
    newtup
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

  def emptyCheck(ref: Int): Boolean = {
    val FuncDecl(ins, out) = funcs.getOrEmpty(fname(ref)).head
    var isempty = false
    if(ins.isEmpty){
      isempty = true
    }
    isempty
  }
}
