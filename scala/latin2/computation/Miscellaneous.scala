package latin2.computation

import info.kwarc.mmt.api._
import objects.{Stack, _}
import info.kwarc.mmt.api.execution._
import info.kwarc.mmt.api.checking._
import info.kwarc.mmt.api.uom._
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.lf._
import lf._
import info.kwarc.mmt.api.objects.OMV


object BetaRun extends ExecutionRule(Apply.path){
   override def under: List[GlobalName] = List()
   override def priority = -100
   /**
    * This has to exist to maintain order for side effects in execution
    * e.g. if we have a mutable variable x, we have to reduce x to its value before passing it into
    * another function ("call by value")
    */
   override def apply(controller: Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term = prog match {
      case ApplySpine(f,args) =>
         val argsE = args map callback.execute
         val fE = callback.execute(f)
         val res = recurse(fE,argsE)(controller)
         if(res.hasheq(ApplySpine(fE,argsE:_*))){
            return res
         }else{
            return callback.execute(res)
         }
   }

   /**
    * makes the assumption that reduction is possible, which should be guaranteed by the typechecker
    * Note that if an incorrect type gets produced by a computation rule, this function will still substitute for it!
    * i.e. we make the assumption that
    * f : a->b->...->z, args: (a,b,...) holds.
    * @param f
    * @param args
    * @param controller
    * @return
    */
   def recurse(f : Term, args: List[Term])(implicit controller: Controller): Term = (f,args) match  {
      case (Lambda(x, a, t), s :: rest) =>
            recurse(t ^? Sub(x , s), rest)
      case (f, Nil) =>
         //all arguments were used, recurse in case f is again a redex
         //otherwise, return f (only possible if there was a reduction, so no need for 'if (reduced)')
         f
      case (f, rest) =>
         // this case is if the term exists but has no definiens that goes down to
         // lambda, for example "cons 1 empty" cons is reducible using apply, iff cons is defined, otherwise
         // it should be treated as a constant "container like"
       ApplySpine(f,rest :_*)
   }
}

/**
 * Prints the input as a side effect
 */
object PrintRun  extends ExecutionRule(IOOps.print.path) {
   override def under: List[GlobalName] =List(Apply.path)
   
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term = {
      prog match {
         case IOOps.print(_ ,a ) =>
            val aE = callback.execute(a)
            println(controller.presenter.asString(aE))
            UnitType.unit
      }
   }
}

/**
 * runs a while-loop.
 * We assume the body changes the condition as a side effect
 */
object WhileRun extends ExecutionRule(WhileOps.`while`.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term= {
      prog match {
         case WhileOps.`while`(cond,body) =>{
            while(term_to_bool(callback.execute(cond))){
               callback.execute(body)
            }
            UnitType.unit
         }
      }
   }
   def term_to_bool(term:Term)={
      term match {
         case Truth._true(_) => true
         case Falsity._false(_) => false
      }
   }
}

/**
 * Subtracts two numbers,
 * Should be removed
 */
object MinusRun extends ExecutionRule(CF.minus.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.minus(t1,t2) =>
            val t1E = callback.execute(t1)
            val t2E = callback.execute(t2)
            // t1E+t2E
            (t1E, t2E) match {
               case (OMLIT(vl:BigInt,tp1),OMLIT(vr:BigInt,tp2)) => {
                  return OMLIT((vl-vr), tp1)
               }
               //case (OMSemiFormal((t1:Text)::_),OMSemiFormal((t2:Text)::_)) => {
               //   return OMLIT(t1.obj.toInt-t2.obj.toInt,NatNums.)
               //}
            }

      }
   }
}
/**
 * adds two numbers,
 * Should be removed
 */
object PlusRun extends ExecutionRule(CF.plus.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.plus(t1,t2) =>
            val t1E = callback.execute(t1)
            val t2E = callback.execute(t2)
            // t1E+t2E
            (t1E, t2E) match {
               case (OMLIT(vl:BigInt,tp1),OMLIT(vr:BigInt,tp2)) => {
                  return OMLIT((vl+vr), tp1)
               }
               //case (OMSemiFormal((t1:Text)::_),OMSemiFormal((t2:Text)::_)) => {
               //   return OMLIT(t1.obj.toInt-t2.obj.toInt,NatNums.)
               //}
            }

      }
   }
}

/**
 * if then else.
 * Should be removed?
 */
object IfRun extends ExecutionRule(IfThenElse.ifte.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case IfThenElse.ifte(tp,b,t1,t2) =>
            val cond = callback.execute(b) match {
               case Conjunction.and(Truth._true(_),Truth._true(_)) =>
                  Truth._true.term
               case Conjunction.and(_,_) =>
                  Falsity._false.term
               case x => x
            }
            cond match {
               case Truth._true(_) =>
                  callback.execute(t1)
               case Falsity._false(_) => callback.execute(t2)
            }
      }
   }
}

/**
 * Greater-than or equals to between two numbers.
 * Should be removed
 */
object GeRun extends ExecutionRule(CF.ge.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.ge(l,r) =>
            val lE  = callback.execute(l)
            val rE  = callback.execute(r)
            (lE, rE) match{
               case (OMLIT(vl:BigInt,tp1),OMLIT(vr:BigInt,tp2)) => {
                  // val vl = vl_string.toInt
                  // val vr = vr_string.toInt
                  if(vl > vr){
                     return Truth._true.term
                  }
                  Falsity._false.term
               }
            }
      }
   }
}
/**
 * to between two numbers.
 * Should be removed
 */
object EqRun extends ExecutionRule(CF._eq.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF._eq(l,r) =>
            val lE = callback.execute(l)
            val rE = callback.execute(r)
            lE match {
               case OMLIT(v1 : BigInt,rt1) => rE match {
                  case OMLIT(v2 : BigInt,rt2) => {
                     if(v1 == v2)
                        Booleans.tt
                     else Booleans.ff
                  }
               }
            }
      }
   }
}


/**
 * sequencing two actions, with the return value being the _last_ functions return value
 */
object SequenceRun extends ExecutionRule(SequencingOps.sequence.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case SequencingOps.sequence(tp1,tp2,fst,snd) =>
          val fstE = callback.execute(fst)
          val sndE = callback.execute(snd)
          sndE
      }
   }
}



object consRun extends ExecutionRule(ListComputation.cons.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.cons(tp,hd, rest) =>
            val hdE = callback.execute(hd)
            val restE = callback.execute(rest)
            ListComputation.cons(tp,hdE,restE)
      }
   }
}

object foldRun extends ExecutionRule(ListComputation.fold.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.fold(tpLs, tpOut, initVal, fun, ls) =>
            val lsE = callback.execute(ls)
            val result = recursive(callback, lsE,fun,initVal)
            // now recurse on the overall result (i.e. simplify the stack of functions generated by the foldLeft
            callback.execute(result)
      }
   }
   private def recursive(callback: ExecutionCallback, tmL : Term, f : Term, initVal: Term): Term ={
      tmL match{
         case ListComputation.cons(tp, hd, rst) => callback.execute(ApplyGeneral(f, recursive(callback, rst,f, initVal)::hd::Nil))
         case ListComputation.empty(tp) => initVal
      }
   }

}

object takeRun extends ExecutionRule(ListComputation.take.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.take(tpLs, num, ls) =>
            val lsE = callback.execute(ls)
            val numE = callback.execute(num) match{case OMLIT(num : BigInt, _) => num}
            val res = recursive(numE, lsE)
            res
      }
   }
   private def recursive(n:BigInt, lsE: Term): Term ={
      lsE match{
         case ListComputation.cons(tp, hd, rst) =>
            if(n==0)
               ListComputation.empty(tp)
            else
               ListComputation.cons(tp,hd,recursive(n-1,rst))
         case ListComputation.empty(tp) => ListComputation.empty(tp)
      }
   }
}

object dropRun extends ExecutionRule(ListComputation.drop.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.drop(tpLs, num, ls) =>
            val lsE = callback.execute(ls)
            val numE = callback.execute(num) match{case OMLIT(num : BigInt, _) => num}
            recursive(numE,lsE)
      }
   }
   private def recursive(n:BigInt, lsE: Term): Term ={
      lsE match{
         case ListComputation.cons(tp, hd, rst) =>
            if(n==0)
               ListComputation.cons(tp,hd,rst)
            else
               recursive(n-1,rst)
         case ListComputation.empty(tp) => ListComputation.empty(tp)
      }
   }
}


object getRun extends ExecutionRule(ListComputation.get.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.get(tpLs, ls, idx) =>
            val idxE = callback.execute(idx) match {
               case OMLIT(vl: BigInt, tp1) => vl.intValue
            }
            val returnOpt = callback.execute(ls)
            recursive(idxE,returnOpt)
      }
   }
   private def recursive(n:BigInt, lsE: Term): Term ={
      lsE match{
         case ListComputation.cons(tp, hd, rst) =>
            if(n==0)
               OptionTypes.just(tp,hd)
            else
               recursive(n-1,rst)
         case ListComputation.empty(tp) => OptionTypes.none(tp)
      }
   }
}
object foldOptionRun extends ExecutionRule(OptionTypes.fold.path){
   override def under = List(Apply.path)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case OptionTypes.fold(tp1,tp2, noneElem, justMap, opt) => {
            val optE = callback.execute(opt)
            // Now we match
            optE match {
               case OptionTypes.just(tp, elem) => callback.execute(ApplyGeneral(callback.execute(justMap), List(optE)))
               case OptionTypes.none(tp) =>  {
                  callback.execute(noneElem)
               }
            }
         }
      }
   }
}


/**
 * variance rule for
 * 1. void is subtype of everything
 * 2. theory includes form a subtyping relationship for theories-as-classes
 * 3. Options pass the inheritance down to the wrapped type
 */
object tmVariance extends VarianceRule(TypedTerms.tm.path){
   val under = List(Apply.path)
   /**
    * pre all arguments covered
    *
    * @return Some(b) if the judgment was proved/disproved, None if the result is inconclusive
    */
   override def apply(solver: Solver)(tp1: Term, tp2: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
      val TypedTerms.tm(a) = tp1
      val TypedTerms.tm(b) = tp2
      a match {
         case EmptyType.void(_) =>
            Some(true)
         case TheoriesAsClasses.typedInstances(OMMOD(theory)) => {
            b match {
               case TheoriesAsClasses.typedInstances(OMMOD(theory_lower)) => {
                  val theory_parse = solver.getModule(theory)
                  theory_parse match{
                     case Some(thy) => Some(thy.asInstanceOf[Theory].getIncludesWithoutMeta.contains(theory_lower))
                     case _ => None
                  }
               }
               case _ => Some(false)
            }
         }//...//solver.check(Subtyping())
         case OptionTypes.option(x) =>
            val OptionTypes.option(y) = b
            Some(solver.check(objects.Subtyping(stack,x,y)))
         case _ => None
      }
   }
}

/**
 * Turns an option value into its underlying, throwing an exception on trying to unwrap None
 */
object unsafeFromJustRun extends ExecutionRule(UnsafeOptions.unsafeFromJust.path){
   override def under = List(Apply.path)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case UnsafeOptions.unsafeFromJust(tp1, opt) => {
            val optE = callback.execute(opt)
            // Now we match
            optE match {
               case OptionTypes.just(tp, elem) => elem
               case OptionTypes.none(tp) =>  {
                  throw MMTException(optE)
               }
            }
         }
      }
   }
}
