package latin2.sfol

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.utils._
//import info.kwarc.mmt.api.uom._
import objects._
//import modules._
//import symbols._
//import libraries._
import frontend._
import info.kwarc.mmt.lf._
import lf._
//import lf._Option.map
import TypedEquality.equal
//import Conjunction.and
//import Disjunction.or
//import Negation.not
//import Equivalence.equiv
//import Implication.impl
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
class SFOLTermGenerator(controller: Controller, mp: MPath) {
  import SFOLPatterns._

  //we save the criteria as a global variable and is fed on execution of the Generator() method
  //that means the generator can be resetted with new criterias, but within the same theory
  var crit: GenCriteria = _

  //logic mode is automatically set when no theory is present, allowing for the generation of logic expressions
  //without the need of a filler theory
  var logmode = false

  var rnd = new Random()
  //logicmode is a flag that can be used to set the generator into a mode that produces logical formulae only,
  //without requiring a theory. Logical variables are treated as atomic formulae
  //user can define how many different variables should be used when initializing the generator

  val theory = new SFOLTheoryAdapter(controller, mp)

  var tps = theory.getTypeSyms
  var funs = theory.getFunSyms
  var lits = theory.getLiterals
  var pred = theory.getPredSyms

  //generation of variables for terms, called x1 ... xn
  var variables = List[OMV]()

  //initialisation of all required lists and maps. fname simply saves all globalnames of function symbols in a list,
  //fnamem saves the global names in relation to the output type for easier access if a specific type is requested.
  //ftypes is a list of all output types that exist in a theory
  //funcs saves the GlobalName and the corresponding type in LF syntax (required to build the terms later)
  //pname and preds does the same, but for predicate symbolds.
  //liter is a hashmap of literals (generated in usable function form), and saves them corresponding to the output
  //type (makes access easier again)
  var fname = List[GlobalName]()
  var fnamea = List[GlobalName]()
  var ftypes = List[Term]()
  var ftypesa = List[Term]()
  var fnamem = new HashMapToSet[Term, GlobalName]
  var funcs = new HashMapToSet[GlobalName, Term]
  var pname = List[GlobalName]()
  var preds = new HashMapToSet[GlobalName, Term]
  var liter = new HashMapToSet[Term,(Complexity, Term)]
  var lname = List[GlobalName]()
  var qname = List[GlobalName]()

  //initialization of SFOL functions
  initLogic()

  //terms and forms are HashMaps that save generated tuples of Complexity object and terms in correspondence with their
  //output type. terms for Terms, forms for formulas. Kinda redundand for formulas, as those are all props anyway,
  //we can propably use them in terms. Or we use forms for atomic formulas specifically, might be useful
  var terms = new HashMapToSet[Term,(Complexity, Term)]
  var forms = mutable.HashSet[(Complexity, Term)]()
  var quants = mutable.HashSet[(Complexity, Term)]()

  //if incremented depth is used, these counters will be utilized
  var tdepth = 0
  var dinct = 0
  var dsect = 0
  var fdepth = 0
  var dincf = 0
  var dsecf = 0

  //Predicates and functions are read out from a theory here
  if(funs.isEmpty){
    throw new RuntimeException("Error: Theory contains no Function symbols")
  }
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
  println("Init functions: " + funs)
  var types = mutable.HashSet[Term]()
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
      types += out
  }
  ftypes = types.toList
  println("Functions: " + fnamem)
  //two makeTerms functions - one creates a stream of terms, the other a stream of (complexity, term) tuples
  //consider making the formula generator a seperate function, as it requires its own term list to generate formulas
  //considering that, while the MMT sees both as the same type, IRL classification has differences and usage is
  //distinctive enough to justify this as well

  def Generator(Criteria: GenCriteria): Stream[Term] ={
    //Generator(Criteria) is top level function and used to initialize the generator according to the Criterias.

    crit = Criteria //CriteriaCheck(Criteria)
    initialize()
    if(crit.min > 0) tdepth = crit.min

    //first we check if a template exists within the criteria.
    //If not, then we use the regular Formulae or Term generation
    if(crit.template != null){
      TemplateGenerator()
    }
    else if(crit.form){
      FormulaGenerator()
    }
    else{
      TermGenerator()
    }
  }

  def TemplateGenerator(): Stream[Term] = {
    generatebyTemplate(crit.template)._2 #:: TemplateGenerator()
  }

  def generatebyTemplate(template: TermTemplate): (Complexity, Term) = {
    dsecf = 0
    dsect = 0
    var newterm: Term = null
    var newcomp: Complexity = null
    var newtup: (Complexity, Term) = null
    var avar = mutable.HashSet[(OMV,Term)]()
    var bvar = mutable.HashSet[(OMV,Term)]()
    if(template.continoustemplate.nonEmpty){
      //handling of continuous levels
      val op = template.continoustemplate.head
      val nltemp = new TermTemplate(template.template, template.substitutions, template.continoustemplate.tail)
      if(qname.contains(op._1)){
        //todo: handling of quantifiers. Only a single quantifier at the time is supported, and that quantifier
        // will be applied until all variables are bound
        newtup = generatebyTemplate(nltemp)
        newtup._1.variables.foreach(v => avar += v)
        newterm = newtup._2
        if (op._1 == TypedUniversalQuantification.forall.path) {
          while(avar.toList.length > bvar.toList.length){
            var tobind = avar.toList.filterNot(v => bvar.contains(v)).head
            newterm = forall(tobind._2, Lambda(tobind._1.name, tm(tobind._2), newterm))
            bvar += tobind
          }
        }
        else if (op._1 == TypedExistentialQuantification.exists.path) {
          var tobind = avar.toList.filterNot(v => bvar.contains(v)).head
          newterm = exists(tobind._2, Lambda(tobind._1.name, tm(tobind._2), newterm))
          bvar += tobind
        }
        else {
          var tobind = avar.toList.filterNot(v => bvar.contains(v)).head
          newterm = existsUnique(tobind._2, Lambda(tobind._1.name, tm(tobind._2), newterm))
          bvar += tobind
        }
      }
      else if(lname.contains(op._1)){
        //handling of logical function symbols except quantifiers
        newtup = generatebyTemplate(nltemp)
        newterm = newtup._2
        newtup._1.variables.foreach(v => avar += v)
        var i = requestNumber(op._3, op._2)
        while(i > 0){
          var args = newterm :: List[Term]()
          if(op._1 != Negation.not.path){
            newtup = generatebyTemplate(nltemp)
            args = newtup._2 :: args
            newtup._1.variables.foreach(v => avar += v)
          }
          newterm = ApplyGeneral(OMS(op._1), args)
          i -= 1
        }
      }
      else{
        //handling of theory specific function symbols
        println(op._1)
        val FuncDecl(ins, out) = funcs(op._1).head
        var i = requestNumber(op._3, op._2)
        newtup = generatebyTemplate(nltemp)
        newterm = newtup._2
        newtup._1.variables.foreach(v => avar += v)
        while(i > 0){
          var args = newterm :: List[Term]()
          while(ins.length > args.length){
            newtup = generatebyTemplate(nltemp)
            args = newtup._2 :: args
            newtup._1.variables.foreach(v => avar += v)
          }
          newterm = ApplyGeneral(OMS(op._1), args)
          i -= 1
        }
        //val symbol = funcs(op._1).head
      }
    }
    else{
      //code for the handling of absolute templates. Variables can be substituted (indicated by flag) with literals (0),
      //generated terms (1), generated formulas (2) or ignored (else).
      newterm = template.template
      for(t <- template.substitutions){
        val substi = {
          var s: (Complexity, Term) = null
          if(t._3 == 0) {
            s = liter(t._2).toList(requestNumber(liter(t._2).toList.length))
          }
          else if (t._3 == 1){
            val types =  ftypes.filterNot(n => crit.excludedtypes.contains(n))
            s = generateTerm(requestDepth(crit), types(requestNumber(types.length)))
          }
          else if(t._3 == 2){
            s = generateFormula(requestDepth(crit))
          }
          else if(t._3 == 3){
            s = generatebyTemplate(t._4)
          }
          else{
            s = (new Complexity(0, t._2, (t._1, t._2) :: List[(OMV, Term)](), List[GlobalName]()), t._1)
          }
          s._1.variables.foreach(v => avar += v)
          s
        }
        val sub = Sub(t._1.name, substi._2) //substi
        newterm = newterm^sub
      }
    }
    //depth and type are irrelevant for the template method, we just have to write somthing in
    newcomp = new Complexity(0, null, avar.toList, List[GlobalName](), bvar = bvar.toList)
    (newcomp, newterm)
  }

  def TermGenerator(): Stream[Term] ={
    //we use this construction to request a randomized, but specific depth for the next term in case
    //backward generation is used. We also test if the min and max values are legit.
    //todo: Perhaps pull that one out and use a initiator method for the stream, so that the test doesn't happen
    //todo: every single time.
    //todo: Wait. We actually might need that here after all. Think about that.
    //todo: redefine Crit.max, where 0 is single variable/literal, -1 is unrestricted.
    val Crit: GenCriteria = {
      if(crit.form) crit.tc
      else crit
    }

    dsect = 0

    if(Crit.escalation){
      //we increment the generation depth when the step number is reached, up to the maximum depth
      if((Crit.escdepth == dinct) && (tdepth < Crit.max)){
        tdepth += 1
        dinct = 0
      }
      else dinct += 1
    }

    val rdepth = {
      if(Crit.mode == 0){
        if(Crit.escalation){
          tdepth
        }
        else requestDepth(Crit)
      }
      else 0
    }
    val rtype = {
      if(crit.mode == 0) ftypesa(requestNumber(ftypesa.length))
      else null
    }
    generateTerm(rdepth, rtype)._2 #:: TermGenerator()
  }

  def generateTerm(rdepth: Int, rtype: Term): (Complexity, Term) ={
    //mode == 0 indicates backward generation, meaning only the requested type is generated and returned. input types
    //are also requested backwards. Requires (some) initialization
    //rtype is a requested type the term should be off (e.g. "latin:/?Nat"), important for backward generation
    //symbol is also important for backward generation, to allow for enforcement of function symbol alterations
    //standard mode is forward generation
    //todo: What do we have to generate and save or return? Init that here
    //we have to generate a new complexity, the term we want to return and the tuple of the two
    val Crit: GenCriteria = {
      if(crit.form) crit.tc
      else crit
    }
    var newterm: Term = null
    var newcom: Complexity = null
    var newtup = (newcom, newterm)
    var newvar = mutable.HashSet[(OMV, Term)]()
    var newsym = mutable.HashSet[GlobalName]()
    var newdepth = 0
    //implementation of backward generation. backward is only called if mode is selected and a type is requested
    if(Crit.mode == 0){
      //error handling: backward generation called, but no type requested
      /*if(fnamem(rtype).toList.isEmpty && liter(rtype).toList.isEmpty){
        throw new RuntimeException("Error: There are no functions to produce terms for the requested type.")
      }*/

      val fops = fnamem(rtype).toList.filterNot(n => Crit.exclusionlist.contains(n))
      //in backward generation we have 2 cases. The requested term depth is not zero, in which case a recursive call
      //is required for subterm generation. If the requested depth is 0, a literal or a variable is returned
      if(rdepth != 0){
        newdepth = rdepth
        var r = requestNumber(fops.length)
        val opname = fops(requestNumber(fops.length))
        val op = funcs.getOrEmpty(opname).head //extract operator by Globalname
        val FuncDecl(ins, out) = op
        //adding the operator to the hashmap for the new complexity object
        newsym += opname
        //with depthmax and depthmin = 0 there are no constraints regarding depth. If constraints are given, we
        //have to regenerate depth until the constraints are hit.
        //generate all input terms for the new term. The maximal depth is 1 smaller then the current maximum, the
        //minimum is zero as we have to generate inputs down to the smallest possible term (literal or variable) here
        //the input terms are saved in the inputs list
        //
        var inputs: List[Term] = Nil
        if(ins.nonEmpty){
          //we pre determine the depth of subterms here. One of them is set to be n-1, as to ensure depth n
          val subdepth = Array.fill[Int](ins.length)(0)
          r = requestNumber(subdepth.length)
          val j = r
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
            val term = {
              generateTerm(subdepth(i), t)
              //if(i == j)else generateTerm(subdepth(i), t, null, nfalt)
            }
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
            throw new RuntimeException("Error: There are neither literals nor variables available to produce terms.")
          }
        }
        if(varli < Crit.rat){
          val r = requestNumber(variables.length)
          newterm = variables(r)
          newtup = (new Complexity(0, rtype, (variables(r), rtype) :: newvar.toList, newsym.toList), newterm)
        }
        else{
          //OMLIT(getLiteral(tp), liter(tp).head)
          //since we already saved a complexity/literal tuple during generation, we can directly use it
          newtup = liter(rtype).toList(requestNumber(liter(rtype).toList.length))
        }
      }

      escalate(Crit)

      //since we generate terms from up to down and don't reuse old terms, we don't have to save the tuple in the
      //hashmap
      newtup
      //if mode is not 0, forward generation is applied, meaning all types are generated, and only requested type is
      //returned.
      //implementation of forward generation
    }
    else{

      val fops = {
        var symbols = List[GlobalName]()
        if(Crit.excludedtypes.nonEmpty) ftypes.filterNot(t => Crit.excludedtypes.contains(t)).foreach(t =>
          symbols = fnamem(t).toList.filterNot(n => Crit.exclusionlist.contains(n)) ++ symbols)
        else symbols = fname.filterNot(n => Crit.exclusionlist.contains(n))
        symbols
      }

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
          var trnd = requestNumber(fops.length)
          //todo: We avoid using empty functions for now, until we clarify
          /*breakable{
            while(true){
              trnd = requestNumber(fops.length)
              val FuncDecl(ins, out) = funcs.getOrEmpty(fops(trnd)).head
              if(ins.nonEmpty){
                break()
              }
            }
          }*/
          val FuncDecl(ins, out) = funcs.getOrEmpty(fops(trnd)).head
          //println("Ins" + ins)
          //interms gets the types of the required input terms to build the new term and maps them against the available
          //terms
          //todo: Here we have to add a chance that literals are used. We have to consider the number of literals we
          //todo: insert here. Interms has ultimately to contain both regular terms and literals
          //todo: Also, we have to make complexities for the literals (probably upon generation)

          //todo: idea! use user given ratio to generate new list with random literals and use it here
          val interms = ins.map(tp =>
            terms(tp).toList //::: liter(tp).toList
          )
          //to get a list of the possible terms we can use for inputs, we map interms against the already generated
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
          //println("Newdepth: " +newdepth)
          //println("depth of escalation: " +tdepth)
          //println("Arguments: " + inputs)
          newterm = ApplyGeneral(OMS(fops(trnd)), inputs)
          newcom = new Complexity(newdepth, out, newvar.toList, newsym.toList)
          newtup = (newcom, newterm)
          if((newcom.depth <= Crit.max) && ((!Crit.escalation) || (newcom.depth == tdepth))){
            terms(out) += newtup
          }

          escalate(Crit)

          //we check here if the generated term fulfilles constraints that might exit, and whether or not their are
          //constraints at all. If the term fulfilles the constraints, or there are no constraints, we break the loop
          //and can return the term
          //println("We are generating")
          if(((newcom.depth <= Crit.max) || (Crit.max == -1)) && (newcom.depth >= Crit.min)
            && ((!Crit.escalation) || (newcom.depth == tdepth)) && ftypesa.contains(out))
          {
            break()
          }

          //Safety block for escalating syntax depth. Automatically escalates the depth after x generations without
          //yielding a useful term. Will abort generation at all after x generations on max depth without yielding
          //a useful term

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
  def FormulaGenerator(): Stream[Term] = {
    //todo: Possibly make this an init method to prepare atomic formulas. A stream can also be prepared here, so that
    //todo: atomic formulas are returned. How many Atomic Formulas should we generate here?
    val init = FormulaInit()
    if(crit.max == 0){
      init
    }
    else if(crit.skipatomics || (crit.quantmin > 0) || (crit.min > 0) || (crit.mode == 2)){
      generateFormulas()
    }
    else init #::: generateFormulas()
  }

  //initialization method, to pre produce a number of atomic formulas for general formula construction later
  def FormulaInit(): Stream[Term] = {
    var formulas = List[Term]()
    if(!logmode){
      for(i <- 1 to crit.atomicformulas){
        formulas = makeAtomicFormula()._2 :: formulas
      }
    }
    else{
      forms = terms(Propositions.prop.term)
      forms.foreach(t => formulas = t._2 :: formulas)
    }
    formulas.toStream
  }

  def generateFormulas(): Stream[Term] = {
    //todo: Request depth for backward generation? Return atomic formula if rdepth is 0?
    var rdepth = 0
    dsecf = 0
    val quantify = {
      if(requestNumber(100) > crit.quantors) false
      else true
    }
    if(crit.escalation){
      //we increment the generation depth when the step number is reached, up to the maximum depth
      if((crit.escdepth == dincf) && (fdepth < crit.max)){
        fdepth += 1
        dincf = 0
      }
      else dincf += 1
    }
    //if(crit.mode == 2){
      //generateFormulaHorn()._2 #:: generateFormulas()
    //}
    if(crit.mode == 0){
      rdepth = {
        if(crit.escalation){
          fdepth
        }
        else{
          var depth = requestNumber(crit.max)
          while(rdepth < crit.min){
            depth = requestNumber(crit.max)
          }
          depth
        }
      }
    }
    generateFormula(rdepth, quantify)._2 #:: generateFormulas()
  }

  def generateFormula(rdepth: Int = 0, quantify: Boolean = false): (Complexity, Term) = {
    //todo: Possible criterias:
    // alternations between quantifiers (should save then the last used quantifier).
    // Quantors on/off
    // syntax depth escalation
    // number of connectives (should we use a min max system here again?)
    // number of free variables/bound variables
    // special form: CNF (a1 or a2 or ...) and (a1 or not a2 or ...) and ...
    // pure logic mode: initialize logical variables (we could forgo a theory in that mode)
    //initialization of all necessary variables for the new complexity object
    //filter operators by exclusionlist
    val fops = lname.filterNot(n => crit.exclusionlist.contains(n))
    var newform: Term = null
    var newcom: Complexity = null
    val lsym: GlobalName = null
    var lquant: GlobalName = null
    var bvar = List[(OMV, Term)]()
    var newtup = (newcom, newform)
    var newvar = mutable.HashSet[(OMV, Term)]()
    var newsym = mutable.HashSet[GlobalName]()
    var newdepth = 0
    var qualt = 0
    var falt = 0
    var inputs = List[Term]()
    //mode selection: 0 is backward generation, else forward generation
    if (crit.mode == 0) {
      //implementation of backward generation
      newdepth = rdepth
      //determine logical operator
      var trnd = requestNumber(fops.length)
      //sub formula initialization and generation. Base case makes atomic formula, else recursive sub formula generation
      var f1: (Complexity, Term) = null
      var f2: (Complexity, Term) = null
      val qfy = {
        if(!logmode && !crit.quanttop && (requestNumber(100) > crit.quantors)) false
        else true
      }
      if (rdepth == 0) {
        if(!logmode){
          f1 = makeAtomicFormula()
        }
        else{
          val atomics = terms(Propositions.prop.term).toList
          f1 = atomics(requestNumber(atomics.length))
        }
      }
      else {
        f1 = generateFormula(rdepth - 1)
        f2 = {
          if (fops(trnd) != Negation.not.path) {
            generateFormula(requestNumber(rdepth), qfy)
          }
          else null
        }
      }
      f1._1.variables.foreach(v => newvar += v)
      inputs = f1._2 :: inputs
      if (f2 != null) {
        f2._1.variables.foreach(v => newvar += v)
        inputs = f2._2 :: inputs
      }
      if (rdepth == 0) {
        //base case: atomic formula, no operator required
        newform = f1._2
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lsym, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      else {
        newsym += fops(trnd)
        newform = ApplyGeneral(OMID(fops(trnd)), inputs) //and(f1._2, f2._2)
        newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, lsym, lquant, qualt, bvar)
        newtup = (newcom, newform)
      }
      //checking flag ensures only top level get's quantified. We only quantify if enough variables exist if free var
      //minimum is given
      if (quantify && (newtup._1.getUnbound().length > crit.minfreevars)) {
        //determine number of applied quantifiers.
        var min = {
          if((newtup._1.getUnbound().length <= crit.maxfreevars) || (crit.maxfreevars == -1)) 0
          else newtup._1.getUnbound().length - crit.maxfreevars
        }
        var max = {
          if(newtup._1.getUnbound().length <= crit.minfreevars) 0
          else newtup._1.getUnbound().length - crit.minfreevars
        }
        var tobind = requestNumber(max, min)
        //the generator will attempt to ensure the usage of minimal quantifier alteration. If, however, not enough
        //free variables are available, there will be simply as many alterations as possible (soft criteria)
        max = {
          if((tobind < crit.quantmax) || (crit.quantmax == -1)) tobind
          else crit.quantmax
        }
        min = {
          if(tobind <= crit.quantmin) tobind
          else crit.quantmin
        }
        //qalc: counter for the number of still applicable alterations.
        var qalc = requestNumber(max, min)
        val aq = qname.filterNot(q => crit.exclusionlist.contains(q))
        var quantifier = aq(requestNumber(aq.length))
        var uvar = newtup._1.getUnbound()
        while (tobind != 0) {
          while((qalc > 0) && (quantifier == lquant)){
            quantifier = aq(requestNumber(aq.length))
          }
          //take one of the unbound variables out and add it to the bound variables. Then bind it.
          val nvar = uvar(requestNumber(uvar.length))
          uvar = uvar.filterNot(q => q == nvar)
          bvar = nvar :: bvar

          if (quantifier == TypedUniversalQuantification.forall.path) {
            if ((lquant != TypedUniversalQuantification.forall.path) && (lquant != null)) {
              qalc -= 1
              qualt += 1
            }
            newsym += TypedUniversalQuantification.forall.path//GlobalName(TypedUniversalQuantification._path, TypedUniversalQuantification._name)
            newform = forall(nvar._2, Lambda(nvar._1.name, tm(nvar._2), newform))
          }
          else if (quantifier == TypedExistentialQuantification.exists.path) {
            if ((lquant != TypedExistentialQuantification.exists.path) && (lquant != null)) {
              qalc -= 1
              qualt += 1
            }
            newsym += TypedExistentialQuantification.exists.path//GlobalName(TypedExistentialQuantification._path, TypedExistentialQuantification._name)
            newform = exists(nvar._2, Lambda(nvar._1.name, tm(nvar._2), newform))
          }
          else {
            if ((lquant != TypedUniqueExistentialQuantification.existsUnique.path) && (lquant != null)) {
              qalc -= 1
              qualt += 1
            }
            newsym += TypedUniqueExistentialQuantification.existsUnique.path//GlobalName(TypedUniqueExistentialQuantification._path, TypedUniqueExistentialQuantification._name)
            newform = existsUnique(nvar._2, Lambda(nvar._1.name, tm(nvar._2), newform))
          }
          lquant = quantifier
          tobind -= 1
        }
      }
      newcom = new Complexity(newdepth, f1._1.output, newvar.toList, newsym.toList, null, lquant, qualt, bvar)
      newtup = (newcom, newform)

      escalate(crit)

      newtup
    }
    else {
      //implementation of forward generation
      breakable {
        while (true) {
          inputs = List[Term]()
          var op = {
            if(quantify){
              val aq = qname.filterNot(q => crit.exclusionlist.contains(q))
              aq(requestNumber(aq.length))
            }
            else fops(requestNumber(fops.length))
          }
          //get the formula('s). We only require 2 formulas in half the cases.
          val f1 = {
            if (!quantify) {
              val l = {
                if(!crit.quanttop) forms.toList ::: quants.toList
                else forms.toList
              }
              var f = l(requestNumber(l.length))
              while ((f._1.depth >= crit.max) && (crit.max != -1)) {
                f = l(requestNumber(l.length))
              }
              f
            }
            else {
              //we apply quantifiers only on the outermost level to simplify generation a bit
              //Else here combines formula list with a list of quantor applied formulas.
              val l = forms.toList ::: quants.toList
              var f = l(requestNumber(l.length))
              //todo: Consider alteration criteria! Should we allow for a minimum of alterations? Also, do we perhaps want
              //todo: a certain number of unbound variables.
              while (f._1.getUnbound().isEmpty || ((f._1.quantalt > crit.quantmax) && (crit.quantmax != -1))) {
                f = l(requestNumber(l.length))
              }
              bvar = f._1.boundVars
              qualt = f._1.quantalt
              lquant = f._1.lastquant
              f
            }
          }
          val f2 = {
            if (!quantify && (op != Negation.not.path)) {
              var f = forms.toList(requestNumber(forms.toList.length))
              while ((f._1.depth >= crit.max) && (crit.max != -1)) {
                f = forms.toList(requestNumber(forms.toList.length))
              }
              f
            }
            else null
          }
          //prepare new complexity values
          f1._1.variables.foreach(v => newvar += v)
          inputs = f1._2 :: inputs
          //we don't count quantifiers against the depth. This is of course factually not correct, but we ultimately care
          //only about the depth of the quantified formula, not the quantifiers themselves.
          if (!quantify) {
            newdepth = f1._1.depth + 1
          }
          else newdepth = f1._1.depth
          if (f2 != null) {
            f2._1.variables.foreach(v => newvar += v)
            inputs = f2._2 :: inputs
            if (f2._1.depth + 1 > newdepth) {
              newdepth = f2._1.depth + 1
            }
          }
          newsym += op
          if (!quantify) {
            newform = ApplyGeneral(OMID(op), inputs) //and(f1._2, f2._2)
          }
          //todo: atm we are not yet checking for the free variable number already existing. We have to add that.
          // handle freevars as maximum number of free variables. => only return if freevarnum <= freevars
          else {
            if (f1._1.lastquant != op) {
              qualt += 1
            }
            lquant = op
            val wvar = f1._1.getUnbound()
            val nvar = wvar(requestNumber(wvar.length))
            bvar = nvar :: bvar
            if (op == TypedUniversalQuantification.forall.path) {
              //fall
              //we extract all unbound variables from the term, choose one at random and apply our quantor
              newform = forall(nvar._2, Lambda(nvar._1.name, tm(nvar._2), f1._2))
            }
            else if (op == TypedExistentialQuantification.exists.path) {
              //exist
              newform = exists(nvar._2, Lambda(nvar._1.name, tm(nvar._2), f1._2)) //makeForall(nvar, Nat.nat.term, f1._2)
            }
            else {
              //existU
              newform = existsUnique(nvar._2, Lambda(nvar._1.name, tm(nvar._2), f1._2))
            }
          }
          newcom = new Complexity(newdepth, Propositions.prop.term, newvar.toList, newsym.toList, null, lquant, qualt, bvar)
          newtup = (newcom, newform)
          if(((newcom.depth <= crit.max) || (crit.max == -1)) && ((qualt < crit.quantmax) || (crit.quantmax == -1))
            && ((!crit.escalation) || (newcom.depth == fdepth))){
            if(!quantify) forms += newtup
            else quants += newtup
          }
          //we check here if the generated term fulfilles constraints that might exit, and whether or not their are
          //constraints at all. If the term fulfilles the constraints, or there are no constraints, we break the loop
          //and can return the term
          //println("We are generating")
          escalate(crit)
          if(((newcom.depth <= crit.max) || (crit.max == -1)) && ((qualt < crit.quantmax) || (crit.quantmax == -1))
            && (newcom.depth >= crit.min) && ((!crit.escalation) || (newcom.depth == fdepth))
            && (newcom.getUnbound().length >= crit.minfreevars) &&
            ((newcom.getUnbound().length <= crit.maxfreevars) || (crit.maxfreevars == -1)))
          {
            break()
          }
        }
      }
      newtup
    }
  }

  //def makeForall(v: OMV, tp: Term, body: Term) = forall(tp, Lambda(v.name,tm(tp), body))

  def generateFormulaHorn(): (Complexity, Term) = {
    var workform = makeAtomicFormula()
    var newform: Term = workform._2
    var newcom: Complexity = null
    val lquant: GlobalName = TypedUniversalQuantification.forall.path
    var bvar = mutable.HashSet[(OMV, Term)]()
    var newtup = (newcom, newform)
    var newvar = mutable.HashSet[(OMV, Term)]()
    workform._1.variables.foreach(v => newvar += v)
    var newsym = mutable.HashSet[GlobalName]()
    var newdepth = 0
    val qualt = 0
    var falt = 0
    //generate random number of terms to use in conjunctions, requires a given maximum
    //we request the depth of the Horn Clause here. 0 generates a fact clause, otherwise we make a implication form
    var trnd = requestNumber(crit.max)
    while(newdepth < trnd){
      workform = makeAtomicFormula()
      workform._1.variables.foreach(v => newvar += v)
      newform = Conjunction.and.apply(newform, workform._2)
      newdepth += 1
    }
    workform = makeAtomicFormula()
    workform._1.variables.foreach(v => newvar += v)
    //application of implication if the depth is larger 0
    if(trnd > 0){
      newform = Implication.impl.apply(newform, workform._2)
      newdepth += 1
      falt += 1
    }
    else{
      newform = workform._2
    }
    //workform._1.variables.foreach(v => newvar += v)
    //newform = Implication.impl.apply(newform, workform._2)
    //apply All-quantifier
    for(v <- newvar.toList){
      newform = forall(v._2, Lambda(v._1.name,tm(v._2), newform))
      bvar += v
    }
    newcom = new Complexity(newdepth, workform._1.output, newvar.toList, newsym.toList, null, lquant, qualt, bvar.toList)
    newtup = (newcom, newform)
    newtup
  }

  def makeAtomicFormula(): (Complexity, Term) = {
    //init for new complexity values. Since most things are pretty set with atomic formulas, we can use vals here
    val depth = 0
    val newvar = mutable.HashSet[(OMV, Term)]()
    var newsym = List[GlobalName]()
    val newout = Propositions.prop.term
    //todo: the ratio from the criteria could be used here to skew generation towards equality, as I could see situations
    //todo: where equality might be a tad more interesting then predicates
    var trnd = requestNumber(100)
    //todo: we have to make and return the complexity object as well, as we require it for further generation down the
    //todo: line
    //todo: we have to randomize the requested term depth in case of backward term generation
    //Formula-generation uses ratio to determine how many atomic formulas use predicates vs equality
    //80 means 80% of formulas use equality
    if(trnd > crit.rat){
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
            val rdepth = {
              if(crit.tc.mode == 0){
                requestDepth(crit.tc)
              }
              else 0
            }
            val newterm = generateTerm(rdepth, tp)
            newterm._1.variables.foreach(v => newvar += v)
            args = newterm._2 :: args
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
      trnd = requestNumber(ftypesa.length)
      var tp = ftypesa(trnd)
      var rdepth = {
        if(crit.tc.mode == 0){
          requestDepth(crit.tc)
        }
        else 0
      }
      val t1 = generateTerm(rdepth, tp)
      rdepth = {
        if(crit.tc.mode == 0){
          requestDepth(crit.tc)
        }
        else 0
      }
      val t2 = generateTerm(rdepth, tp)
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

  def makeVars(n: Int): List[OMV] = {
    //todo: rework variable generation such that the same variable name is not used for several data types
    //makes n variables
    val v = new mutable.HashSet[OMV]
    if(n == 1){
      v += OMV("x")
    }
    else for(i <- 1 to n){
      val x = OMV("x"+i)
      v += x
    }
    v.toList
  }
  //todo: we may delete this, as we are not using this anymore
  /*def emptyCheck(ref: Int): Boolean = {
    val FuncDecl(ins, out) = funcs.getOrEmpty(fname(ref)).head
    var isempty = false
    if(ins.isEmpty){
      isempty = true
    }
    isempty
  }*/

  //method to request a random depth for backward generation calls
  def requestDepth(Crit: GenCriteria): Int ={
    var rdepth = 0
    if(Crit.max > -1 || Crit.min > 0){
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
  def requestNumber(mod: Int, min: Int = 0): Int = {
    var number = -1
    if(mod < 0){
      throw new RuntimeException("requestNumber requires non negative modifiers")
    }
    else if(mod == 0){
      0
    }
    else{
      while(number < min){
        number = rnd.nextInt()%mod
        if(number < 0){
          number *= -1
        }
      }
      number
    }
  }

  def initialize() = {

    logmode = crit.logmode

    rnd = new Random()

    variables = makeVars(crit.varnum)

    ftypesa = ftypes.filterNot(t => crit.excludedtypes.contains(t))

    liter = new HashMapToSet[Term,(Complexity, Term)]

    terms = new HashMapToSet[Term,(Complexity, Term)]
    forms = mutable.HashSet[(Complexity, Term)]()
    quants = mutable.HashSet[(Complexity, Term)]()

    tdepth = 0
    dinct = 0
    dsect = 0
    fdepth = 0
    dincf = 0
    dsecf = 0

    if(crit.escalation){
      if(crit.mode == 0){
        if(crit.form){
          fdepth = crit.min
          tdepth = crit.tc.min
        }
        else tdepth = crit.min
      }
    }

    //todo: this might be better back at the top init, since the predicates and functions don't change through criterias
    // the literals and variables do, though
    if(!logmode){
      println("Init Literals: ")
      lits.foreach{
        case(tp, rt) =>
          println(rt.semType)
          val raw = rt.semType.enumerate(1)
          println(raw)
          val rawlits = rt.semType.enumerate(1).get //OrElse {Nil}
          //println("making literal ")// + rawlits.toList.head)
        var i = 0
          while(i < crit.litnum){
            val lit = OMLIT(rawlits.next, rt)//rt.semType.enumerate(0).getOrElse(Nil) //.map(v => rt.of(v))
            val com = new Complexity(0, tp, mutable.HashSet[(OMV, Term)]().toList, mutable.HashSet[GlobalName]().toList)
            println("new literal: " + lit)
            liter += (tp, (com, lit))
            i += 1
          }
        //val values = rt.semType.enumerate(0).getOrElse(Nil)
        //val lits = values map {v => rt(v)}
      }
      println("Init variables:")
      funs.foreach {
        case (p, tp) =>
          val FuncDecl(ins, out) = tp
          //we apply the variables to every distinct input universe to generate the most
          //basic term of each universe, which is a single variable
          //part of initialisation, as those are permanent
          ins.distinct.foreach(t => for (i <- 1 to variables.length) {
            val c = new Complexity(0, t, List[(OMV, Term)]((variables(i - 1), t)), List[GlobalName]())
            terms += (t, (c, variables(i - 1)))//(t, terdep)
          })
      }
    }
    else{
      //initialize propositional variables for logic mode
      println("Init propositional variables:")
      val t = Propositions.prop.term
      for (i <- 1 to variables.length) {
        val c = new Complexity(0, t, List[(OMV, Term)]((variables(i - 1), t)), List[GlobalName]())
        val tup = (c, variables(i - 1))
        terms += (t, tup)
        forms += tup
      }
    }
    println("Init complete!")
  }

  def CriteriaCheck(Criteria: GenCriteria): GenCriteria ={
    //todo: implement method to check criteria for legitimacy/legality/contradictions
    //todo: things to check:
    // - min depth > max depth
    println("Checking Criteria...")
    if((Criteria.varnum < 0) || (Criteria.litnum < 0)){
      throw new RuntimeException("Error: Negative variable or literal number")
    }
    if((Criteria.varnum == 0) && (Criteria.litnum == 0)){
      throw new RuntimeException("Error: Variable and Literal number both 0.")
    }
    if((Criteria.min > Criteria.max) && (Criteria.max > 0)){
      throw new RuntimeException("Error: The requested minimal depth is larger then the requested maximum depth.")
    }
    if((Criteria.max < 0) && (Criteria.mode == 0)){
      throw new RuntimeException("Error: Backward generation can't be called without limiting the maximum depth.")
    }
    if((Criteria.quantmin > Criteria.quantmax) && (Criteria.quantmax > -1)){
      throw new RuntimeException("Error: Quantifier alterations min and max inconsistent.")
    }
    if((Criteria.minfreevars > Criteria.maxfreevars) && (Criteria.maxfreevars > -1)){
      throw new RuntimeException("Error: free variable min and max inconsistent.")
    }
    if(!Criteria.form && logmode){
      throw new RuntimeException("Error: Logic mode active, but theory term requested.")
    }
    if(Criteria.tc != null){
      if(Criteria.tc.template != null){
        throw new RuntimeException("Error: Embedded criteria can not contain template.")
      }
      if(!Criteria.form){
        throw new RuntimeException("Error: Term criteria contains more criteria.")
      }
      if(Criteria.tc.form){
        throw new RuntimeException("Error: Formula criteria contains more formula criteria.")
      }
      val sub = CriteriaCheck(Criteria.tc)
    }
    if(Criteria.template != null){
      TemplateCheck(Criteria.template)
    }
    println("Criteria check complete!")
    Criteria
  }

  def TemplateCheck(template: TermTemplate): Unit ={
    println("Checking Template...")
    var i = 0
    while(i < template.continoustemplate.length){
      if(i != 0){
        if(qname.contains(template.continoustemplate(i)._1)){
          throw new RuntimeException("Error: Only continuoustemplate(0) can contain a quantifier.")
        }
        if((template.continoustemplate(i)._1 == TypedEquality.equal.path)
          || preds.getOrEmpty(template.continoustemplate(i)._1).nonEmpty){
          throw new RuntimeException("Error: continuoustemplate can't contain predicates or equality.")
        }
        i += 1
      }
    }
    println("Template check complete!")
  }

  def generatectemp(): (Term, List[(OMV, Term, Int, TermTemplate)]) = {
    var list = List[(OMV, Term, Int, TermTemplate)]()
    list = (OMV("x"), Propositions.prop.term, 2, null) :: list
    val tup = (list.head._1, list)
    tup
  }
  //example template
  def generateHornTemplate(): TermTemplate = {

    var forallconti = List[(GlobalName, Int, Int)]()
    var andconti = List[(GlobalName, Int, Int)]()

    val a = OMV("a")
    val x = OMV("x")
    val y = OMV("y")
    //and template initialization

    val andterm = x
    andconti = (Conjunction.and.path, 1, 5) :: andconti
    var andlist = List[(OMV, Term, Int, TermTemplate)]()
    andlist = (x, Propositions.prop.term, 2, null) :: andlist

    val andtemp = new TermTemplate(andterm, andlist, andconti)

    val implication = Implication.impl.apply(a, y)
    forallconti = (TypedUniversalQuantification.forall.path, 0, 0) :: forallconti
    var foralllist = List[(OMV, Term, Int, TermTemplate)]()
    foralllist = (a, Propositions.prop.term, 3, andtemp) :: foralllist
    foralllist = (y, Propositions.prop.term, 2, null) :: foralllist

    val foralltemp = new TermTemplate(implication, foralllist, forallconti)
    foralltemp
  }

  def generateTemplate(): (Term, List[(OMV, Term, Int, TermTemplate)]) = {
    var list = List[(OMV, Term, Int, TermTemplate)]()
    list = (OMV("a"), Nat.nat.term, 0, null) :: list
    list = (OMV("t"), Nat.nat.term, 1, null) :: list
    list = (OMV("x"), Nat.nat.term, 3, null) :: list

    var op: Term = null
    var opname: GlobalName = null
    //the breakable loop here ensures that requested terms with a depth > 0 don't use functions without input

    opname = fnamem(Nat.nat.term).toList(1)
    op = funcs.getOrEmpty(opname).head //extract operators Globalname

    var inputs = List[Term]()
    inputs = list.head._1 :: list(1)._1 :: inputs

    //ins.foreach(tp => generateTerm(1, tp, 0, max-1))
    var newterm = ApplyGeneral(OMS(opname), inputs)
    inputs = List[Term]()
    inputs = newterm :: list(2)._1 :: inputs
    newterm = ApplyGeneral(OMS(opname), inputs)
    val tup = (newterm, list)
    tup
  }

  def initLogic(): Unit ={
    //initializes lists of GlobalNames for logical function symbols and Quantifiers
    lname = Conjunction.and.path :: lname
    lname = Disjunction.or.path :: lname
    lname = Equivalence.equiv.path :: lname
    lname = Implication.impl.path :: lname
    lname = Negation.not.path :: lname
    qname = TypedUniversalQuantification.forall.path :: qname
    qname = TypedExistentialQuantification.exists.path :: qname
    qname = TypedUniqueExistentialQuantification.existsUnique.path :: qname
  }

  def escalate(Crit: GenCriteria): Unit = {
    if(Crit.escalation){
      if(Crit.form){
        dsecf += 1
        if(dsecf > Crit.sescdepth){
          if(fdepth == Crit.max){
            throw new RuntimeException(Crit.sescdepth +" terms where generated, but didn't meet criteria. Maximum depth reached. Abort!")
          }
          println(Crit.sescdepth +" terms where generated, but didn't meet criteria. Escalating syntactic depth to " +(fdepth+1))
          fdepth += 1
          dincf = 0
          dsecf = 0
        }
      }
      else{
        dsect += 1
        if(dsect > Crit.sescdepth){
          if(tdepth == Crit.max){
            throw new RuntimeException(Crit.sescdepth +" terms where generated, but didn't meet criteria. Maximum depth reached. Abort!")
          }
          println(Crit.sescdepth +" terms where generated, but didn't meet criteria. Escalating syntactic depth to " +(tdepth+1))
          tdepth += 1
          dinct = 0
          dsect = 0
        }
      }
    }
  }

  def manualescalation(esc: Int): Unit ={
    //todo: term depth, formula depth,
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
