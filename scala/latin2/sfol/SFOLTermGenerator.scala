package latin2.sfol

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.utils._
import info.kwarc.mmt.api.uom._
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
import scala.util.control.Breaks._


class SFOLTermGenerator(controller: Controller, mp: MPath, varnum: Int = 3) {
  import SFOLPatterns._
  val rnd = new Random()
  //user can define how many different variables should be used when initializing the generator
  val varlim = varnum
  val theory = new SFOLTheoryAdapter(controller, mp)

  val tps = theory.getTypeSyms
  //tps foreach {case (p,_) =>
  //  println("type symbol " + p.name)
  //}
  val funs = theory.getFunSyms
  val lits = theory.getLiterals

  //generation of variables for terms, called x1 ... xn
  val variables = makeVars(varlim)
  //println("Variables:")
  //println(variables)
  var fname = List[GlobalName]()
  val funcs = new HashMapToSet[GlobalName, Term]
  //todo: define interestingness further for complexity
  //eg number of equal symbols/variables on both sides of a symbol
  val terms = new HashMapToSet[Term,(Complexity, Term)]
  //todo: check how to access the literals
  println("Literals: " + lits)

  lits.foreach{
    case(a, rt) =>
      val k = rt.semType.enumerate(0).getOrElse(Nil) //.map(v => rt.of(v))
      println(k)
      //k.toList.foreach(println())
      //k.foreach(println(rt.semType.toString()))
  }
  //todo: end of literal code

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
  //consider making the formula generator a seperate function, as it requires its own term list to generate formulas
  //considering that, while the MMT sees both as the same type, IRL classification has differences and usage is
  //distinctive enough to justify this as well

  //standard values of null, 0, 0 will return Terms with no restrictions regarding type and syntax tree depth
  def makeTerms(tp: Term = null, min: Int = 0, max: Int = 3): Stream[Term] = {
    newTerm(tp, min, max)._2 #:: makeTerms(tp, min, max)
  }

  def makeTermsInfo(tp: Term = null, min: Int = 0, max: Int = 0): Stream[(Complexity, Term)] = {
    newTerm(tp, min, max) #:: makeTermsInfo(tp, min, max)
  }

  def newTerm(tp: Term, min: Int, max: Int): (Complexity, Term) = {
    //newTerm is called with the requested type, as well as the minimal and the maximal depth of the term
    if(funcs.isEmpty){
      println("There are no functions to generate terms with.")
      System.exit(0)
      //todo: exit program?
    }
    //conditionals that allow for more specific term generation, such as:
    //returing only terms of a specific type
    //returning only terms within a specified tree depth
    var requestedtype = tp
    var minimalcomp = min
    var maximumcomp = max

    //todo: init newterm und newcom here
    //initialization with null values in preparation for the conditional loop
    var newterm: Term = null
    var newcom: Complexity = null
    var newtup = (newcom, newterm)
    //todo: start the loop from here
    //todo: we have to check for the requested term type, as well for the minimal and maximal term depth
    breakable{
      while(true){
        //potential way to implement this: make the whole thing a while loop and check the conditions at the end
        //of the generation. if all conditions are met, break the loop to return the term, otherwise the term is simply
        //saved for later usage and another term is generated.
        //for maximum term length, another condition could be added to check beforehand if the new would term exceed it and
        //to discard it entirely (as terms larger then the max will never be used, in return or generation)

        var newdepth = 0
        //using Hashsets for generation of variable and symbol list for new complexity, to avoid duplicates
        var newvar = mutable.HashSet[Term]()
        var newsym = mutable.HashSet[GlobalName]()
        var trnd = rnd.nextInt()%funcs.toList.length
        if(trnd < 0){
          trnd *= -1
        }
        var empty = emptyCheck(trnd)

        //todo: delete special case, funcs without input are ok. Instead check if it is an empty func and handle it

        while(empty){
          trnd = rnd.nextInt()%funcs.toList.length
          if(trnd < 0){
            trnd *= -1
          }
          empty = emptyCheck(trnd)
        }
        val FuncDecl(ins, out) = funcs.getOrEmpty(fname(trnd)).head

        //println("Ins" + ins)
        //interms gets the types of the required input terms to build the new term
        val interms = ins.map(tp =>
          terms(tp).toList
        )
        //to get a list of the possible terms we can use for inputs, we map interms against the llready generated
        //terms
        val args = interms.map{
          list =>
            var arg = List[Term]()
            list.foreach {
              tup =>
                //we only take terms that, at most, are one below the requested depth. If there is no max specified, we
                //can take them all
                if(tup._1.depth < max || max == 0){
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
        //we fill inputs randomly with exactly the number of required arguments, using already generated terms
        val inputs = {
          //first we generate a list with input arguments for the term
          //I am assuming here that the order of the ins and the order of args are
          //going to be the same. Might turn out to be wrong.
          var m = List[Term]()
          var j = 0
          while(m.length < args.length){
            //println("args: " + args)
            //todo: check if I actually need a type check here, as args might have several types as elements
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
        newterm = ApplyGeneral(OMS(fname(trnd)), inputs)
        newcom = new Complexity(newdepth, newvar.toList, newsym.toList)
        newtup = (newcom, newterm)
        terms(out) += newtup
        //we check here if the generated term fulfilles constraints that might exit, and whether or not their are
        //constraints at all. If the term fulfilles the constraints, or there are no constraints, we break the loop
        //and can return the term
        if(((newterm == requestedtype) || (requestedtype == null)) && ((newcom.depth <= maximumcomp)
              || (maximumcomp == 0)) && (newcom.depth >= minimalcomp))
        {
          break()
        }
        //println("new term: " + newterm.toStr(false))
        //terms.foreach(a => println(a))
        // make a random new term for each function symbol
      }
    }
    newtup
  }

  //todo: implement function, that generates and returns a stream of formulas, like the term generator
  //todo: problem: Formula generator requires term generator. Where should that be initialized?
  //todo: possible solution: make top level function the initializer, then a recursive helper function that uses
  //todo: that function. Or require the user to the Stream of terms (benefit: User get to specify the terms)
  def makeFormulas(): Stream[Term] = {
    val baseTerms = makeTerms()
    makeFormStream(baseTerms)
  }

  def makeFormStream(baseTerms: Stream[Term]): Stream[Term] = {
    newFormula(baseTerms) #:: makeFormStream(baseTerms)
  }

  def newFormula(baseTerms: Stream[Term]): Term = {
    null
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
