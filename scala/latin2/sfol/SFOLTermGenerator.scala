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
import TypedEquality.equal
import Conjunction.and
import Disjunction.or
import Negation.not
import Equivalence.equiv
import Implication.impl
import TypedExistentialQuantification.exists
import TypedUniqueExistentialQuantification.existsUnique
import TypedUniversalQuantification.forall
import info.kwarc.mmt.moduleexpressions.operators.TypedTerms.tm

import scala.collection.mutable
//import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.util.Random
//import latin2.sfol.Complexity
import scala.util.control.Breaks._

//git@gl.mathhub.info:MMT/LATIN2.git
class SFOLTermGenerator(controller: Controller, mp: MPath, varnum: Int = 3, litnum: Int = 3) {
  import SFOLPatterns._
  val rnd = new Random()
  //user can define how many different variables should be used when initializing the generator
  val theory = new SFOLTheoryAdapter(controller, mp)

  val tps = theory.getTypeSyms
  //tps foreach {case (p,_) =>
  //  println("type symbol " + p.name)
  //}
  val funs = theory.getFunSyms
  val lits = theory.getLiterals
  val pred = theory.getPredSyms

  //generation of variables for terms, called x1 ... xn
  val variables = makeVars(varnum)
  //val literals = initLit(lits)
  //println("Variables:")
  //println(variables)
  //initialisation of all required lists and maps. fname simply saves all globalnames of function symbols in a list,
  //fnamem saves the global names in relation to the output type for easier access if a specific type is requested.
  //funcs saves the GlobalName and the corresponding type in LF syntax (required to build the terms later)
  //pname and preds does the same, but for predicate symbolds.
  //liter is a hashmap of literals (generated in usable function form), and saves them corresponding to the output
  //type (makes access easier again)
  var fname = List[GlobalName]()
  val fnamem = new HashMapToSet[Term, GlobalName]
  val funcs = new HashMapToSet[GlobalName, Term]
  var pname = List[GlobalName]()
  val preds = new HashMapToSet[GlobalName, Term]
  var liter = new HashMapToSet[Term,(Complexity, Term)]
  //todo: define interestingness further for complexity
  //eg number of equal symbols/variables on both sides of a symbol
  //terms and forms are HashMaps that save generated tuples of Complexity object and terms in correspondence with their
  //output type. terms for Terms, forms for formulas. Kinda redundand for formulas, as those are all props anyway,
  //we can propably use them in terms. Or we use forms for atomic formulas specifically, might be useful
  val terms = new HashMapToSet[Term,(Complexity, Term)]
  val forms = mutable.HashSet[(Complexity, Term)]()
  val quants = mutable.HashSet[(Complexity, Term)]()
  var ttf: Stream[(Complexity, Term)] = _
  println("Init Predicates: " + pred)
  pred.foreach{
    case(p, tp) =>
      println("predicate symbol " + p.name)
      println("type in LF syntax: " + tp)
      val PredDecl(ins) = tp
      println("inputs: " + ins.mkString(", "))

      pname = p::pname
      preds += (p, tp)
  }
  println("Init Literals: " + lits)
  lits.foreach{
    case(tp, rt) =>
      println(rt.semType)
      val rawlits = rt.semType.enumerate(1).get //OrElse {Nil}
      println("making literal ")// + rawlits.toList.head)
      var i = 0
      while(i <= litnum){
        val lit = OMLIT(rawlits.next, rt)//rt.semType.enumerate(0).getOrElse(Nil) //.map(v => rt.of(v))
        val com = new Complexity(0, tp, mutable.HashSet[(OMV, Term)]().toList, mutable.HashSet[GlobalName]().toList)
        println("new literal: " + lit)
        liter += (tp, (com, lit))
        i += 1
      }
      //val values = rt.semType.enumerate(0).getOrElse(Nil)
      //val lits = values map {v => rt(v)}
  }
  println("Init Functions: " + funs)
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
      fnamem += (out, p)
      funcs += (p, tp)

      //we apply the variables to every distinct input universe to generate the most
      //basic term of each universe, which is a single variable
      //part of initialisation, as those are permanent
      ins.distinct.foreach(t => for (i <- 1 to variables.length) {
        val c = new Complexity(0, t, List[(OMV, Term)]((variables(i - 1), t)), List[GlobalName]())
        terms += (t, (c, variables(i - 1)))//(t, terdep)
      })
    //println("Terms:")
    //terms.foreach(a => println(a))
  }
  println("Functions: " + fnamem)

  //two makeTerms functions - one creates a stream of terms, the other a stream of (complexity, term) tuples
  //consider making the formula generator a seperate function, as it requires its own term list to generate formulas
  //considering that, while the MMT sees both as the same type, IRL classification has differences and usage is
  //distinctive enough to justify this as well

  //todo: Add template based generation. Get help with substitution.
  //substitution: term ^ subs
  //
  //subs = Substitution(...)
  //todo: Add new criterias to generation process
  //todo: Research translation of e.g. "ax + c" to MMT terms

  def Generator(Crit: GenCriteria): Stream[Term] ={
    if(Crit.form){
      FormulaGenerator(Crit)
    }
    else{
      TermGenerator(Crit)
    }
  }

  def TermGenerator(Crit: GenCriteria): Stream[Term] ={
    //we use this construction to request a randomized, but specific depth for the next term in case
    //backward generation is used. We also test if the min and max values are legit.
    //todo: Perhaps pull that one out and use a initiator method for the stream, so that the test doesn't happen
    //todo: every single time.
    //todo: Wait. We actually might need that here after all. Think about that.
    //todo: redefine Crit.max, where 0 is single variable/literal, -1 is unrestricted.
    val rdepth = {
      if(Crit.mode == 0){
        requestDepth(Crit)
      }
      else 0
    }
    generateTerm(rdepth, Crit)._2 #:: TermGenerator(Crit)
  }

  def generateTerm(rdepth: Int = 0, Crit: GenCriteria): (Complexity, Term) ={
    //mode == 0 indicates backward generation, meaning only the requested type is generated and returned. input types
    //are also requested backwards. Requires (some) initialization
    //tp is the requested type (e.g. "latin:/?Nat")
    //standard mode is forward generation
    //todo: What do we have to generate and save or return? Init that here
    //we have to generate a new complexity, the term we want to return and the tuple of the two
    var newterm: Term = null
    var newcom: Complexity = null
    var newtup = (newcom, newterm)
    var newvar = mutable.HashSet[(OMV, Term)]()
    var newsym = mutable.HashSet[GlobalName]()
    var newdepth = 0
    //implementation of backward generation. backward is only called if mode is selected and a type is requested
    if(Crit.mode == 0 && Crit.tp != null){
      //error handling: backward generation called, but no type requested
      if(fnamem(Crit.tp).toList.isEmpty && liter(Crit.tp).toList.isEmpty){
        throw new RuntimeException("There are no functions for the requested type.")
      }
      //in backward generation we have 2 cases. The requested term depth is not zero, in which case a recursive call
      //is required for subterm generation. If the requested depth is 0, a literal or a variable is returned
      if(rdepth != 0){
        newdepth = rdepth
        var op: Term = null
        var opname: GlobalName = null
        var r = 0
        //the breakable loop here ensures that requested terms with a depth > 0 don't use functions without input
        breakable{
          while(true){
            r = requestNumber(fnamem(Crit.tp).toList.length)
            opname = fnamem(Crit.tp).toList(requestNumber(fnamem(Crit.tp).toList.length))
            op = funcs.getOrEmpty(opname).head //extract operators Globalname
            val FuncDecl(ins, out) = op
            if(ins.nonEmpty){
              break()
            }
          }
        }
        //adding the operator to the hashmap for the new complexity object
        newsym += opname
        //with depthmax and depthmin = 0 there are no constraints regarding depth. If constraints are given, we
        //have to regenerate depth until the constraints are hit.
        val FuncDecl(ins, out) = op
        //generate all input terms for the new term. The maximal depth is 1 smaller then the current maximum, the
        //minimum is zero as we have to generate inputs down to the smallest possible term (literal or variable) here
        //the input terms are saved in the inputs list
        //
        var inputs: List[Term] = Nil
        if(ins.nonEmpty){
          //we pre determine the depth of subterms here. One of them is set to be n-1, as to ensure depth n
          val subdepth = Array.fill[Int](ins.length)(0)
          r = requestNumber(subdepth.length)
          subdepth(r) = rdepth - 1
          var i = 0
          while(i < subdepth.length){
            if(subdepth(i) == 0){
              if(rdepth > 1){
                r = requestNumber(rdepth-1)
              }
              else{
                r = 0
              }
              subdepth(i) = r
            }
            i += 1
          }
          i = 0
          for(t <- ins){
            val term = generateTerm(subdepth(i), Crit)
            inputs = term._2 :: inputs
            term._1.variables.foreach(v => newvar += v)
            term._1.symbols.foreach(s => newsym += s)
            i += 1
          }
        }
        //ins.foreach(tp => generateTerm(1, tp, 0, max-1))
        newterm = ApplyGeneral(OMS(opname), inputs)
        newtup = (new Complexity(newdepth, out, newvar.toList, newsym.toList), newterm)
        terms(out) += newtup
      }
      // the else case is the requested depth == 0, meaning we return a literal or variable
      else{
        //using variables/literals according to the chance given in the GenCriteria
        //todo: add possible case for usage of empty function instead of literal
        //todo: we could check if both are empty at init. We could also make a global flag.
        val varli = {
          if(liter.nonEmpty && variables.nonEmpty){
            requestNumber(100)
          }
          else if(liter.nonEmpty){
            1
          }
          else if(variables.nonEmpty){
            0
          }
          else{
            throw new RuntimeException("There are neither literals nor variables to produce terms.")
          }
        }
        if(varli < Crit.rat){
          val r = requestNumber(variables.length)
          newterm = variables(r)
          newtup = (new Complexity(0, Crit.tp, (variables(r), Crit.tp) :: newvar.toList, newsym.toList), newterm)
        }
        else{
          //OMLIT(getLiteral(tp), liter(tp).head)
          //since we already saved a complexity/literal tuple during generation, we can directly use it
          newtup = liter(Crit.tp).toList(requestNumber(liter(Crit.tp).toList.length))
        }
      }
      //since we generate terms from up to down and don't reuse old terms, we don't have to save the tuple in the
      //hashmap
      newtup
      //if mode is not 0, forward generation is applied, meaning all types are generated, and only requested type is
      //returned.
      //implementation of forward generation
    }
    else{
      if(Crit.mode == 0){
        println("Backward generation called, but no type requested. Falling back to forward generation.")
      }
      //we break the loop if no specific type is requested, or if the generated term matches the requested type
      //todo: Forward generation seems to apply one type of function overly often (with nat: natzero). Why? Is the
      //todo: RNG scewed?
      breakable{
        while(true){
          //potential way to implement this: make the whole thing a while loop and check the conditions at the end
          //of the generation. if all conditions are met, break the loop to return the term, otherwise the term is simply
          //saved for later usage and another term is generated.
          //for maximum term length, another condition could be added to check beforehand if the new would term exceed it and
          //to discard it entirely (as terms larger then the max will never be used, in return or generation)

          //using Hashsets for generation of variable and symbol list for new complexity, to avoid duplicates
          newvar = mutable.HashSet[(OMV, Term)]()
          newsym = mutable.HashSet[GlobalName]()
          newdepth = 0
          var trnd = requestNumber(funcs.toList.length)
          //todo: We avoid using empty functions for now, until we clarify
          breakable{
            while(true){
              trnd = requestNumber(fnamem(Crit.tp).toList.length)
              val FuncDecl(ins, out) = funcs.getOrEmpty(fname(trnd)).head
              if(ins.nonEmpty){
                break()
              }
            }
          }
          val FuncDecl(ins, out) = funcs.getOrEmpty(fname(trnd)).head
          //println("Ins" + ins)
          //interms gets the types of the required input terms to build the new term and maps them against the available
          //terms
          //todo: Here we have to add a chance that literals are used. We have to consider the number of literals we
          //todo: insert here. Interms has ultimately to contain both regular terms and literals
          //todo: Also, we have to make complexities for the literals (probably upon generation)

          //todo: idea! use user given ratio to generate new list with random literals and use it here
          val interms = ins.map(tp =>
            (terms(tp).toList) //::: liter(tp).toList
          )
          //to get a list of the possible terms we can use for inputs, we map interms against the llready generated
          //terms. If max is 0, no limit is set and all terms in interms are applicable
          //todo: Error: this is the list of possible terms, not of the used terms. Therefore, checking for newdepth is
          //todo: wrong here. We most likely have to make this the list of com/term tuples, and work with both in inputs
          val args = {
            if(Crit.max == -1) interms
            else{
              interms.map{
                list =>
                  var arg = List[(Complexity, Term)]()
                  list.foreach {
                    tup =>
                      //we only take terms that, at most, are one below the requested depth. If there is no max specified, we
                      //can take them all.
                      //todo: if max i -1, all terms are usable. Take the if outside (if 0, args = interms, else sieve)
                      if(tup._1.depth < Crit.max){
                        arg = tup :: arg
                      }
                  }
                  arg
              }
            }
          }
          //don't forget to add 1 to newdepth, as so far its only the highest input depth, but new depth is that +1
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
              var i = requestNumber(args(j).length) //(k).toList.length
              //println("Index: " + i)
              var t = args(j)(i)
              //todo: variables vs literals
              //to ensure the ratio of variables vs literals we check first if the term we have chosen is a variable.
              //if yes, we do the rnd-ratio check and replace the variable with a literal if the dice feels like it.
              if(variables.contains(t._2)){
                var rnvar = requestNumber(100)
                if(rnvar > Crit.rat){
                  rnvar = requestNumber(liter.toList.length)
                  if(rnvar > Crit.rat){
                    t = liter(t._1.output).toList(rnvar)
                  }
                }
              }
              m = t._2 :: m
              for(v <- t._1.variables){
                newvar+=v
              }
              for(s <- t._1.symbols){
                newsym+=s
              }
              if(t._1.depth > newdepth) newdepth = t._1.depth
              j += 1
            }
            m
          }
          newdepth += 1
          //println("Arguments: " + inputs)
          newterm = ApplyGeneral(OMS(fname(trnd)), inputs)
          newcom = new Complexity(newdepth, out, newvar.toList, newsym.toList)
          newtup = (newcom, newterm)
          terms(out) += newtup
          //we check here if the generated term fulfilles constraints that might exit, and whether or not their are
          //constraints at all. If the term fulfilles the constraints, or there are no constraints, we break the loop
          //and can return the term
          if(((out == Crit.tp) || (Crit.tp == null)) && ((newcom.depth <= Crit.max)
            || (Crit.max == -1)) && (newcom.depth >= Crit.min))
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
  }

  //user method, that prepares and returns first atomic formulas, and then builds more complex ones from them.
  //Formulageneration supports 3 modes -> Forwardgeneration, Backwardgeneration and Hornformulageneration
  //todo: Customizable number of atomic formulas? Option to forgoe the return of atomic formulas?
  def FormulaGenerator(crit: GenCriteria): Stream[Term] = {
    //todo: Possibly make this an init method to prepare atomic formulas. A stream can also be prepared here, so that
    //todo: atomic formulas are returned. How many Atomic Formulas should we generate here?
    val init = FormulaInit(crit)
    if(crit.max == 0){
      init
    }
    else if(crit.skipatomics || (crit.quantmin > 0) || (crit.min > 0) || (crit.mode == 2)){
      generateFormulas(crit)
    }
    else init #::: generateFormulas(crit)
  }

  //initialization method, to pre produce a number of atomic formulas for general formula construction later
  def FormulaInit(crit: GenCriteria): Stream[Term] = {
    var formulas = List[Term]()
    for(i <- 1 to crit.atomicformulas){
      formulas = makeAtomicFormula(crit)._2 :: formulas
    }
    formulas.toStream
  }

  def generateFormulas(crit: GenCriteria): Stream[Term] = {
    //todo: Request depth for backward generation? Return atomic formula if rdepth is 0?
    var rdepth = 0
    if(crit.mode == 2){
      generateFormulaHorn(crit)._2 #:: generateFormulas(crit)
    }
    else if(crit.mode == 0){
      rdepth = requestNumber(crit.max)
      while(rdepth < crit.min){
        rdepth = requestNumber(crit.max)
      }
      //todo: add flag for quantifiers. Check against crit qmax. 1 = quantifiers, 0 = no quantifiers
      generateFormula(rdepth, crit, 1)._2 #:: generateFormulas(crit)
    }
    else generateFormula(rdepth, crit)._2 #:: generateFormulas(crit)
  }

  def generateFormula(rdepth: Int = 0, crit: GenCriteria, quant: Int = 0): (Complexity, Term) = {
    //todo: Possible criterias:
    // alternations between quantifiers (should save then the last used quantifier).
    // number of connectives (should we use a min max system here again?)
    // number of free variables/bound variables
    //initialization of all necessary variables for the new complexity object
    var newform: Term = null
    var newcom: Complexity = null
    var lquant: Int = 0
    var bvar = List[(OMV, Term)]()
    var newtup = (newcom, newform)
    var newvar = mutable.HashSet[(OMV, Term)]()
    var newsym = mutable.HashSet[GlobalName]()
    var newdepth = 0
    var qualt = 0
    //mode selection: 0 is backward generation, else forward generation
    if(crit.mode == 0){
      //implementation of backward generation
      newdepth = rdepth
      //determine logical operator
      var trnd = requestNumber(5)
      //sub formula initialization and generation. Base case makes atomic formula, else recursive sub formula generation
      var f1: (Complexity, Term) = null
      var f2: (Complexity, Term) = null
      if(rdepth == 0){
        f1 = makeAtomicFormula(crit)
      }
      else{
        f1 = generateFormula(rdepth-1, crit)
        val f2 = {
          if(trnd < 4){
            generateFormula(requestNumber(rdepth), crit)
          }
          else null
        }
      }
      f1._1.variables.foreach(v => newvar += v)
      if(f2 != null){
        f2._1.variables.foreach(v => newvar += v)
      }
      if(rdepth == 0){
        //base case: atomic formula, no operator required
        newform = f1._2
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      else if(trnd == 0){
        //conjunction
        newsym += GlobalName(Conjunction._path, Conjunction._name)
        newform = Conjunction.and.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      else if(trnd == 1){
        //disjunction
        newsym += GlobalName(Disjunction._path, Disjunction._name)
        newform = Disjunction.or.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      else if(trnd == 2){
        //equivalence
        newsym += GlobalName(Equivalence._path, Equivalence._name)
        newform = Equivalence.equiv.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      else if(trnd == 3){
        //implication
        newsym += GlobalName(Implication._path, Implication._name)
        newform = Implication.impl.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      else if(trnd == 4){
        //not
        newsym += GlobalName(Negation._path, Negation._name)
        newform = Negation.not(f1._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      //checking flag ensures only top level get's quantified
      if(quant == 1){
        //todo: 4. determine number of bound variables. Add possibility to specify min max number through criteria
        var tobind = requestNumber(newtup._1.getUnbound().length)
        //todo: 5. determine number of quantifier alterations. Add possibility to specify min through criteria
        qualt = requestNumber(crit.quantmax)
        //qalc: counter for the number of still applicable alterations.
        //todo: Consider case: max quantifers larger then bindable variables.
        var qalc = qualt

        while(tobind != 0){
          trnd = requestNumber(3)

          if(trnd == 0){
            if(f1._1.lastquant != 1 && f1._1.lastquant != 0){
              qalc -= 1
            }
            lquant = 1
            val wvar = f1._1.getUnbound()
            val nvar = wvar(requestNumber(wvar.length))
            bvar = nvar :: bvar
            newsym += GlobalName(TypedUniversalQuantification._path, TypedUniversalQuantification._name)
            newform = forall(nvar._2, Lambda(nvar._1.name,tm(nvar._2), newform))
          }
          else if(trnd == 1){
            if(f1._1.lastquant != 2 && f1._1.lastquant != 0){
              qalc -= 1
            }
            lquant = 2
            val wvar = f1._1.getUnbound()
            val nvar = wvar(requestNumber(wvar.length))
            bvar = nvar :: bvar
            newsym += GlobalName(TypedExistentialQuantification._path, TypedExistentialQuantification._name)
            newform = exists(nvar._2, Lambda(nvar._1.name,tm(nvar._2), newform))
          }
          else{
            if(f1._1.lastquant != 3 && f1._1.lastquant != 0){
              qalc -= 1
            }
            lquant = 3
            val wvar = f1._1.getUnbound()
            val nvar = wvar(requestNumber(wvar.length))
            bvar = nvar :: bvar
            newsym += GlobalName(TypedUniqueExistentialQuantification._path, TypedUniqueExistentialQuantification._name)
            newform = existsUnique(nvar._2, Lambda(nvar._1.name,tm(nvar._2), newform))
          }
        }
      }
      newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
      newtup = (newcom, newform)

      newtup
    }
    else{
      //implementation of forward generation
      //todo: implement forward generation
      //todo: 1. determine operator (and, or, not, implication, equivalence, forall, exist, exist unique)
      // also add check if we want no quantifier
      var trnd = requestNumber(8)
      //get the formula('s). We only require 2 formulas in half the cases.
      val f1 = {
        if(trnd < 5){
          var f = forms.toList(requestNumber(forms.toList.length))
          while((f._1.depth >= crit.max) && (crit.max != -1)){
            f = forms.toList(requestNumber(forms.toList.length))
          }
          f
        }
        else{
          //todo: Else here combines formula list with a list of quantor applied formulas. Makes sure that quantors
          //todo: are outermost level
          val l = forms.toList ::: quants.toList
          var f = l(requestNumber(l.length))
          //todo: Consider alteration criteria! Should we allow for a minimum of alterations? Also, do we perhaps want
          //todo: a certain number of unbound variables.
          while(f._1.getUnbound().isEmpty || (f._1.quantalt > crit.quantmax)){
            f = l(requestNumber(l.length))
          }
          bvar = f._1.boundVars
          qualt = f._1.quantalt
          lquant = f._1.lastquant
          f
        }
      }
      val f2 = {
        if(trnd < 4){
          var f = forms.toList(requestNumber(forms.toList.length))
          while((f._1.depth >= crit.max) && (crit.max != -1)){
            f = forms.toList(requestNumber(forms.toList.length))
          }
          f
        }
        else null
      }
      //prepare new complexity values
      f1._1.variables.foreach(v => newvar += v)
      //we don't count quantifiers against the depth. This is of course factually not correct, but we ultimately care
      //only about the depth of the quantified formula, not the quantifiers themselves.
      if(trnd < 5){
        newdepth = f1._1.depth + 1
      }
      else newdepth = f1._1.depth
      if(f2 != null){
        f2._1.variables.foreach(v => newvar += v)
        if(f2._1.depth + 1 > newdepth){
          newdepth = f2._1.depth + 1
        }
      }
      if(trnd == 0){
        //todo: and
        newsym += GlobalName(Conjunction._path, Conjunction._name)
        newform = Conjunction.and.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        forms += newtup
      }
      else if(trnd == 1){
        //todo: or
        newsym += GlobalName(Disjunction._path, Disjunction._name)
        newform = Disjunction.or.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        forms += newtup
      }
      else if(trnd == 2){
        //todo: equiv
        newsym += GlobalName(Equivalence._path, Equivalence._name)
        newform = Equivalence.equiv.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        forms += newtup
      }
      else if(trnd == 3){
        //todo: imp
        newsym += GlobalName(Implication._path, Implication._name)
        newform = Implication.impl.apply(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        forms += newtup
      }
      else if(trnd == 4){
        //todo: not
        newsym += GlobalName(Negation._path, Negation._name)
        newform = Negation.not(f1._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        forms += newtup
      }
      else if(trnd == 5){
        //todo: fall
        //we extract all unbound variables from the term, choose one at random and apply our quantor
        if(f1._1.lastquant != 1 && f1._1.lastquant != 0){
          qualt += 1
        }
        lquant = 1
        val wvar = f1._1.getUnbound()
        val nvar = wvar(requestNumber(wvar.length))
        bvar = nvar :: bvar
        newsym += GlobalName(TypedUniversalQuantification._path, TypedUniversalQuantification._name)
        newform = forall(nvar._2, Lambda(nvar._1.name,tm(nvar._2), f1._2))
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        quants += newtup
      }
      else if(trnd == 6){
        //todo: exist
        if(f1._1.lastquant != 2 && f1._1.lastquant != 0){
          qualt += 1
        }
        lquant = 2
        val wvar = f1._1.getUnbound()
        val nvar = wvar(requestNumber(wvar.length))
        bvar = nvar :: bvar
        newsym += GlobalName(TypedExistentialQuantification._path, TypedExistentialQuantification._name)
        newform = exists(nvar._2, Lambda(nvar._1.name,tm(nvar._2), f1._2)) //makeForall(nvar, Nat.nat.term, f1._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        quants += newtup
      }
      else{
        //todo: existU
        if(f1._1.lastquant != 3 && f1._1.lastquant != 0){
          qualt += 1
        }
        lquant = 3
        val wvar = f1._1.getUnbound()
        val nvar = wvar(requestNumber(wvar.length))
        bvar = nvar :: bvar
        newsym += GlobalName(TypedUniqueExistentialQuantification._path, TypedUniqueExistentialQuantification._name)
        newform = existsUnique(nvar._2, Lambda(nvar._1.name,tm(nvar._2), f1._2))
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar)
        newtup = (newcom, newform)
        quants += newtup
      }
      //todo: 2. get appropriate number of input formulas (we have already initialized atomics)
      //todo:    don't forget to check them for the max criteria's, and unbound variables
      //todo: 3. apply operator, save to hashmap
      //todo: 4. Check for minimal criteria (min, quantmin). Considering dropping min criteria, can't really think
      //todo:    of an application here
      //todo: 5. return formula
      newtup
    }
  }

  def makeForall(v: OMV, tp: Term, body: Term) = forall(tp, Lambda(v.name,tm(tp), body))

  def generateFormulaHorn(Crit: GenCriteria): (Complexity, Term) = {
    //todo: let's start making horn formulas!
    //horn formulas can be produced in disjunction form or implication form. The latter uses conjunctions and
    //should be easier to produce. (p and q and ... => x). Further, there are three types if horn formulas:
    //1: Definite Clauses (p and q and ... and t => u)
    //2: facts (u) (we have to make this)
    //3: goal clauses (p and q and ... and t => false) (we can ignore this)
    //todo: Aren't Horn Formulas conjunctions from 1 or more clauses? So, this is then a clause generator? Important?
    //step 1: use rnd to determine type of formula
    //step 2: produce atomic formulas
    //todo: How can we generate a horn formula. And -> when is a horn formula interesting.
    //todo: Problem -> Horn Formulas are potentially infinite. How can we possibly constraint size of the Formula
    //todo: First try: make a number of clauses (number random within constraint), then apply conjunctions.
    //todo: important: conjunctions are binary operators, we will have to apply n-1 conjunctions (maybe in a loop)
    //todo: Apply implication on another generated clause
    //todo: Apply Quantifiers, such that there are no free variables in the end.
    //todo: Return Formula. Important: Each step has to use and update complexity
    var workform = makeAtomicFormula(Crit)
    var newform: Term = workform._2
    var newcom: Complexity = null
    val lquant: Int = 1
    var bvar = mutable.HashSet[(OMV, Term)]()
    var newtup = (newcom, newform)
    var newvar = mutable.HashSet[(OMV, Term)]()
    workform._1.variables.foreach(v => newvar += v)
    var newsym = mutable.HashSet[GlobalName]()
    var newdepth = 0
    val qualt = 0
    //todo: generate random number of terms to use in conjunctions, requires a given maximum
    //we request the depth of the Horn Clause here. 0 generates a fact clause, otherwise we make a implication form
    var trnd = requestNumber(Crit.max)
    while(newdepth < trnd){
      workform = makeAtomicFormula(Crit)
      workform._1.variables.foreach(v => newvar += v)
      newform = Conjunction.and.apply(newform, workform._2)
      newdepth += 1
    }
    workform = makeAtomicFormula(Crit)
    workform._1.variables.foreach(v => newvar += v)
    //application of implication if the depth is larger 0
    if(trnd > 0){
      newform = Implication.impl.apply(newform, workform._2)
      newdepth += 1
    }
    else{
      newform = workform._2
    }
    workform._1.variables.foreach(v => newvar += v)
    newform = Implication.impl.apply(newform, workform._2)
    //todo: Apply All-quantors
    for(v <- newvar.toList){
      newform = forall(v._2, Lambda(v._1.name,tm(v._2), newform))
      bvar += v
    }
    newcom = new Complexity(newdepth, workform._1.output, newvar.toList, newsym.toList, lquant, qualt, bvar.toList)
    newtup = (newcom, newform)
    newtup
  }

  def makeAtomicFormula(Crit: GenCriteria): (Complexity, Term) = {
    //init for new complexity values. Since most things are pretty set with atomic formulas, we can use vals here
    val depth = 0
    val newvar = mutable.HashSet[(OMV, Term)]()
    var newsym = List[GlobalName]()
    val newout = Propositions.prop.term
    //todo: the ratio from the criteria could be used here to skew generation towards equality, as I could see situations
    //todo: where equality might be a tad more interesting then predicates
    var trnd = rnd.nextInt()%100
    if(trnd < 0){
      trnd *= -1
    }
    //todo: we have to make and return the complexity object as well, as we require it for further generation down the
    //todo: line
    //todo: we have to randomize the requested term depth in case of backward term generation
    //Formula-generation uses ratio to determine how many atomic formulas use predicates vs equality
    //80 means 80% of formulas use equality
    if(trnd > Crit.rat){
      //todo: apply predicate
      trnd = requestNumber(preds.toList.length)
      newsym = preds.toList(trnd)._1 :: newsym
      val PredDecl(ins) = preds.toList(trnd)._2.toList.head
      //todo: two possible approaches - use backward generation to make terms for each input, or use forward generation
      //todo: to pre generate a number of terms to select from.
      val inputs = {
        var args = List[Term]()
        ins.foreach{
          tp =>
            //todo: formulagenerator has to get all the infos the termgenerator gets I guess
            //for every input term of a formula, a new term is generated, according to a GenCriteria object within
            //the GenCriteria object (Critception!), allowing a high customization level for the user
            //for that, a new Criteria object must be generated, based on the old one, as the requested type matters for
            //the input type
            //todo: rethink requested type! Are we requesting that only formulas using specific inputs are generated?
            //todo: rethink requested depth here for backward generation.
            //Currently, we can request a specific type of input terms in the FormulaCriteria object. Is the Term tp
            //even important at that point?
            if(Crit.tp == tp || Crit.tp == null){
              val Criteria =
                new GenCriteria(Crit.tc.mode, tp, Crit.tc.min, Crit.tc.max, Crit.tc.rat, Crit.tc.form, Crit.tc.tc)
              val rdepth = {
                if(Criteria.mode == 0){
                  requestDepth(Criteria)
                }
                else 0
              }
              val newterm = generateTerm(rdepth, Criteria)
              newterm._1.variables.foreach(v => newvar += v)
              args = newterm._2 :: args
            }
        }
        args
      }
      //todo: Complexity object, saving formulas in val forms = new HashMapToSet[Term,(Complexity, Term)]
      val newForm = ApplyGeneral(preds.toList(trnd)._2.toList.head, inputs)
      val newtup = (new Complexity(depth, newout, newvar.toList, newsym), newForm)
      forms += newtup
      newtup
    }
    else{
      //todo: apply typed equality. The Terms have to be of the same type (important)
      //todo: We have to allow for specificaly requested term types in the criteria object
      //todo: Therefor, we have to make a new criteria object. Best we take Crit.tc, save it independently, and then
      //todo: change the requested type there
      //todo: We have to randomize the depth of the terms.
      //todo: We have to allow for forward and backward generation of the terms
      //first, we get random a type for the terms we want to apply equality to. Both terms have to be of the same type
      trnd = requestNumber(fnamem.keys.toList.length)
      var tp = fnamem.keys.toList(trnd)
      if(Crit.tp != null){
        tp = Crit.tp
      }
      val Criteria =
        new GenCriteria(Crit.tc.mode, tp, Crit.tc.min, Crit.tc.max, Crit.tc.rat, Crit.tc.form, Crit.tc.tc)
      var rdepth = {
        if(Criteria.mode == 0){
          requestDepth(Criteria)
        }
        else 0
      }
      val t1 = generateTerm(rdepth, Criteria)
      rdepth = {
        if(Criteria.mode == 0){
          requestDepth(Criteria)
        }
        else 0
      }
      val t2 = generateTerm(rdepth, Criteria)
      //todo: complexity object, saving formulas
      //todo: clarify as equality seems to want x0, x1, x2. Is one of those the type of the others?
      t1._1.variables.foreach(v => newvar += v)
      t2._1.variables.foreach(v => newvar += v)
      val newForm = equal.apply(t1._1.output, t1._2, t2._2)
      val newtup = (new Complexity(depth, newout, newvar.toList, newsym), newForm)
      forms += newtup
      newtup
    }
  }
/*
  def newFormula(): Term = {
    //todo: General Formula generation could include seperate steps of requested formulas, e.g. make some equivalences,
    //todo: then quantify formulas after they were tested.
    //todo: FormulaGenerator() requires, dependent on the generation mode of the terms, a initialization that makes
    //todo: a Stream of Terms, and a Stream of Atomic Formulas, with wich we can generate the more complex Formulas.
    //we get a stream of terms, and generate a stream of formulas
    //we have to use both base terms, as well as existing formulas to make new formulas
    //todo: expand this to allow usage of already generated formulae.
    //todo: Question is, how. Maybe like with the term generator, make an ever expanding hashmaptoset?
    //todo: Predicate symbols, always return propositions
    //todo: Maybe use makeTerm directly instead of the stream
    var trnd = (rnd.nextInt()%funcs.toList.length)%4
    if(trnd < 0){
      trnd *= -1
    }
    var t1 = getTerm()
    if(trnd != 3){
      //check if free variables are available for quantifiers. So far, only the number of variables are compared
      //todo: this could be a too naive approach. Have to think about it
      while(t1._1.getvarnum() == t1._1.getboundnum()){
        t1 = getTerm()
      }
    }
    //todo: get the type of the output somewhere. What's the output of quantifiers?
    //forall
    if(trnd == 0){
      forall.apply(t1._2)
      //todo: the symbollist has to be updated
      //todo: update formula status and bound variables. Clarification regarding when is something a formula required
      var newcomp = new Complexity(t1._1.depth + 1, t1._1.variables, t1._1.symbols)
    }
    //exists
    if(trnd == 1){
      val nt = exists.apply(t1._2)
      var newcomp = new Complexity(t1._1.depth + 1, t1._1.variables, t1._1.symbols)
    }
    //existsunique
    if(trnd == 2){
      val nt = existsUnique.apply(t1._2)
      var newcomp = new Complexity(t1._1.depth + 1, t1._1.variables, t1._1.symbols)
    }
    //equality
    else{
      var t2 = getTerm()
      //check if equality is already present and discard if so to avoid equal chains
      while(t1._1.hasEqual || t2._1.hasEqual){
        if(t1._1.hasEqual){
          t1 = getTerm()
        }
        else{
          t2 = getTerm()
        }
      }
      val nt = equal.apply(t1._2, t2._2)
      val newdepth = {
        if (t1._1.depth > t2._1.depth){
          t1._1.depth + 1
        } else{
          t2._1.depth + 1
        }
      }
      var newcomp = new Complexity(newdepth + 1, t1._1.variables :: t2._1.variables, t1._1.symbols :: t2._1.symbols)
      forms(out) += (newcomp, nt)
    }
  }
*/

  def makeVars(n: Int): List[OMV] = {
    //makes n variables
    val v = new mutable.HashSet[OMV]
    for(i <- 1 to n){
      val x = OMV("x"+i)
      v += x
    }
    v.toList
  }
  //todo: we may delete constants, as internally they are just variables
  def makeCons(): List[Term] = {
    val v = new mutable.HashSet[Term]
    for(i <- 1 to 3){
      val c = OMV("c"+i)
      v += c
    }
    v.toList
  }
  //todo: we may delete this, as we are not using this anymore
  def emptyCheck(ref: Int): Boolean = {
    val FuncDecl(ins, out) = funcs.getOrEmpty(fname(ref)).head
    var isempty = false
    if(ins.isEmpty){
      isempty = true
    }
    isempty
  }

  //method to request a random depth for backward generation calls
  def requestDepth(Crit: GenCriteria): Int ={
    var rdepth = 0
    if(Crit.max > -1 || Crit.min > 0){
      if(Crit.min > Crit.max){
        throw new RuntimeException("The requested minimal depth is larger then the requested maximum depth.")
      }
      if(Crit.max < 0){
        throw new RuntimeException("Backward generation can't be called without limiting the maximum depth.")
      }
      if(Crit.max >= 0){
        rdepth = requestNumber(Crit.max)
        while(Crit.max < rdepth || Crit.min > rdepth){
          //todo: potential error: standard max is 0. What now? That's a problem with backwards generation.
          //todo: possible solution: For backward generation, a maximal depth > 0 could be firmly requested
          rdepth = requestNumber(Crit.max)
        }
      }
    }
    rdepth
  }

  //method to request a non-negative random number. If the modifier is 0, 0 is returned, if > 0, rnd%mod operation.
  def requestNumber(mod: Int): Int = {
    if(mod < 0){
      throw new RuntimeException("requestNumber requires non negative modifiers")
    }
    else if(mod == 0){
      0
    }
    else{
      var number = rnd.nextInt()%mod
      if(number < 0){
        number *= -1
      }
      number
    }
  }

  //a simple method to make a literal

  /*def getLiteral(tp: Term): scala.Iterator[Any] = {
    liter(tp).head.semType.enumerate(0).getOrElse {
      //println("Error getLiteral - enumerate has done something unexpected.")
      //System.exit(0) //exception
      throw new RuntimeException("Error getLiteral - enumerate has done something unexpected.")
    }
  }*/
}
