package latin2.computation

import info.kwarc.mmt.api._
import objects.{Stack, _}
import info.kwarc.mmt.api.execution._
import info.kwarc.mmt.api.checking._
import info.kwarc.mmt.api.uom._
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.symbols.Constant
import info.kwarc.mmt.lf._
import info.kwarc.mmt.lf.structuralfeatures.StructuralFeatureUtils.{NONE, getConstants}
import latin2.computation.consRun.listType
import latin2.computation.takeRun.listType
import lf._

import scala.::


object PrintRun  extends ExecutionRule(IOOps.print.path) {
   override def under: List[GlobalName] =List(Apply.path)
   
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term = {
      prog match {
         case IOOps.print(c ,a ) =>
            val aE = callback.execute(a)
            println(controller.presenter.asString(aE))
            UnitType.unit
      }
   }
}


/*
object DefinedRun extends RulePreprocessor(CF.define.path){
   override def under: List[GlobalName]= List(Apply.path)
   def apply(const : Constant) : Option[ExecutionRule] = {
      const.tp match {
         case Some(TypedEquality.tequal(tp,x,target)) => {
            x match {
               case OMID(gname: GlobalName) => Some(new DefinedRule(gname, target))
            }
         }
         // case _=> None
      }
   }
   override def applicable(tp : Constant): Boolean = tp.rl == Some("Execute")
}*/
object DefinedRun extends RulePreprocessor(RecurseableDefinitions.define.path){
   override def under: List[GlobalName]= List(Apply.path)
   def apply(const : Constant) : Option[ExecutionRule] = {
      const.tp match {
         case Some(RecurseableDefinitions.define(tp,OMID(gname: GlobalName),target : OMBINDC)) => {
            Some(new DefinedRule(gname, target))

         }
         // case _=> None
      }
   }
   // override def applicable(tp : Constant): Boolean = tp.rl == Some("Execute")
}


class DefinedRule(override val head: GlobalName, val targetTerm : OMBINDC) extends ExecutionRule(head){
   override def under: List[GlobalName]= List(Apply.path)
   override def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ApplyGeneral(OMID(head), ls) => {
            val lsE = ls map callback.execute
            val app = ApplyGeneral(targetTerm,lsE)
            //val theory = controller.getTheory(head.module)
            //val simple = controller.simplifier(app, SimplificationUnit(theory.getInnerContext, expandConDefs = false, expandVarDefs = false, fullRecursion = false))

            // fibonacci i = if i>1 then fib i-1 + fib i-2 else print(i); return 1
            // execute myself
            callback.execute(app)
         }
      }
   }
}

/*
object PlusRun extends ExecutionRule(CF.plus.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.plus(t1,t2) =>
          val t1E = callback.execute(t1)
          val t2E = callback.execute(t2)
          // t1E+t2E
          CF.plus(t1E, t2E)
      }
   }
}*/

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
/*
object NewRun extends SyntaxDrivenRule{
   def apply(...){
      prog match{
         case OMPMOD(p, args) =>{
            val i = new MMTInstance(p,args)
            OMLIT(tp,tm)
         }
      }
   }
}
*/
/*
object NewRule extends InferenceRule(TheoriesAsClasses.`new`.path,OfType.path){
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = {
      tm match{
         case TheoriesAsClasses.`new`(OMPMOD(p, args))=>
         Some(TheoriesAsClasses.instance(toTerm(p, args)))
      }
   }
   def toTerm(p :MPath,args : List[Term]):Term = {
      OMA(OMID(p),args)
   }
   /*tm match {
      case CF.typedInstances(OMMOD(p)) =>
         if (!covered) {
            // check that theory p exists, and is allowed to have instances
         }
         Some(Types.tp.term)
   }*/
}*/

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

case class MMTException(tm : Term) extends Exception

object ThrowRun extends ExecutionRule(Exceptions.`throw`.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match {
         case Exceptions.`throw`(tm) => {
            throw new MMTException(tm)
         }
      }
   }
}

object TryCatchRun extends ExecutionRule(Exceptions.tryCatch.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match {
         case Exceptions.tryCatch(tp,term, handler) => {
            try{
               callback.execute(term)
            }catch{
               case MMTException(exc) => callback.execute(ApplyGeneral(handler, exc::Nil))
            }
         }
      }
   }
}

object AssignmentRun extends ExecutionRule(MutableVariables.assign.path){
   override def under = List(Apply.path)
   val instType = new RepresentedRealizedType(instanceMeta.anyInstance.term, InstanceType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case MutableVariables.assign(tp,v1 : OMV,t2) =>
            val t2E = callback.execute(t2)
            env.stack.assign(v1.name, t2E)
            UnitType.unit
         case MutableVariables.assign(tp,TheoriesAsClasses.field(v,OMID(nm)),t2)=>
            val vE = callback.execute(v)
            vE match{
               case TheoriesAsClasses.typedInstance(instType(inst)) =>inst.set(GlobalName(inst.theory.path,nm.name),t2)
            }

            UnitType.unit
         case MutableVariables.assign(tp,n,t2) => {
            ???
         }
      }
   }
}


object DeclareRun extends ExecutionRule(MutableVariables.declare.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback:ExecutionCallback,env:RuntimeEnvironment,prog: Term):Term={
      prog match{
         case MutableVariables.declare(tp1,tp2,initVal, OMBINDC(term, con, scope::Nil)) => {
            // we need to execute the initVal, in case it is not ground yet and contains
            // mutable values
            // TODO: check this later in case you want something like call-by reference
            val eInitVal = callback.execute(initVal)
            env.stack.newVariable(con.variables.head)
            env.stack.assign(con.variables.head.name,eInitVal)
            // execute everything below the declaration with the variable in context
            val executed = callback.execute(scope)
            // now the context is over, we can remove the variable again
            env.stack.removeVariables(1)
            executed
            // executed
         }
      }
   }
}

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

case class ExecutionError(tm : Term) extends Exception

object NewRun extends ExecutionRule(TheoriesAsClasses.`new`.path){
   override def under = Nil
   val instType = RealizedType(instanceMeta.anyInstance.term, InstanceType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case TheoriesAsClasses.`new`(OMMOD(p),initf) =>
            val inst = new InstanceOfTheory(env, controller.getTheory(p))
            val realized = OMLIT(inst,instType)
            val theory = TheoriesAsClasses.typedInstance(realized)
            // the initfun is supposed to mutate the theory for initialisation
            callback.execute(ApplyGeneral(initf,theory::Nil))
            if(check_fully_initialised(inst)) theory
            else throw ExecutionError(theory)
      }
   }
   def check_fully_initialised(theory: InstanceOfTheory): Boolean = {
      // TODO: add an actualy runtime check if necessary
      true
      //theory.theory.getConstants.filter(p => p.df == None).length == 0
   }
}

object FieldRun extends ExecutionRule(TheoriesAsClasses.field.path){
   override def under = List() // Apply.path
   val instType = new RepresentedRealizedType(instanceMeta.anyInstance.term, InstanceType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case TheoriesAsClasses.field(obj,OMID(name)) =>
            val objE = callback.execute(obj)
            objE match{
               case TheoriesAsClasses.typedInstance(instType(inst))=>
                  inst.get(GlobalName(inst.theory.path,name.name)).get
            }
            // this should always exist, since it typechecks

      }
   }

}

object emptyRun extends ExecutionRule(ListComputation.empty.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list.term), execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.empty(tp) =>
            OMLIT(scala.List.empty[Term], listType)
         // this should always exist, since it typechecks

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
            restE match{
               case OMLIT(tail : List[Term],listType) =>  OMLIT(hdE :: tail, listType)
            }
      }
   }
}

object foldRun extends ExecutionRule(ListComputation.fold.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.fold(tpLs, tpOut, initVal, fun, ls) =>
            val result = callback.execute(ls) match {
               case OMLIT(lsE : List[Term], listType) =>
                  lsE.foldLeft(initVal)((x : Term ,y)=>callback.execute(ApplyGeneral(fun,x:: y :: Nil )))
            }
            // now recurse on the overall result (i.e. simplify the stack of functions generated by the foldLeft
            callback.execute(result)
      }
   }
}

object takeRun extends ExecutionRule(ListComputation.take.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.take(tpLs, num, ls) =>
            val lsE = callback.execute(ls) match { case OMLIT(ls : List[Term],listType) => ls}
            val numE = callback.execute(num) match{case OMLIT(num : BigInt, _) => num}
            OMLIT(lsE.take(numE.intValue),listType)
      }
   }
}

object dropRun extends ExecutionRule(ListComputation.drop.path){
   override def under = List(Apply.path)
   val listType = new RepresentedRealizedType(TypedTerms.tm(ListComputation.list),execution.ListType)

   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ListComputation.drop(tpLs, num, ls) =>
            val lsE = callback.execute(ls) match { case OMLIT(ls : List[Term],listType) => ls}
            val numE = callback.execute(num) match{case OMLIT(num : BigInt, _) => num}
            OMLIT(lsE.drop(numE.intValue),listType)
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
               case OMLIT(vl:BigInt,tp1) => vl.intValue
            }
            val returnOpt = callback.execute(ls) match {
               case OMLIT(lsE : List[Term], listType) =>{
                  lsE.lift(idxE)
               }
            }
          returnOpt match {
             case Some(res) => OptionTypes.just(tpLs,res)
             case None => OptionTypes.none(tpLs)
          }
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
 * |- typedInstance OMLIT(instance of theory p) : typedInstances(p)
 */
object InstanceTyping extends InferenceRule(TheoriesAsClasses.typedInstance.path, OfType.path) {
   val instType = RealizedType(instanceMeta.anyInstance.term, InstanceType)
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Option[Term] = {
      tm match {
         case TheoriesAsClasses.typedInstance(instType(Some(inst: InstanceOfTheory))) =>
            Some(TheoriesAsClasses.typedInstances(OMMOD(inst.theory.path)))
      }
   }
}

/**
 * p is a theory that is allowed to be used as a type --->  |- typedInstances p : tp
 */
object InstancesTyping extends InferenceRule(TheoriesAsClasses.typedInstances.path, OfType.path) {
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Option[Term] = {
      tm match {
         case TheoriesAsClasses.typedInstances(OMMOD(p)) =>
            if (!covered) {
               // check that theory p exists, and is allowed to have instances
               // first check whether the theory exists
               val module = solver.getModule(p) match{
                  case None => return None
                  case Some(module) => module
               }
               // solver.solve(p,CF.anyInstance)
            }
            // Some(Types.tp.term)
            Some(Types.tp.term)
      }
   }
}



/**
 * "init" fully initializes the definienses in theory --->  |- new theory init : typedInstances theory
 */
object NewInstance extends InferenceRule(TheoriesAsClasses.`new`.path, OfType.path) {
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Option[Term] = {
      tm match {
         case TheoriesAsClasses.`new`(theory, initfun) => {
            if (!covered) {
               val tp: OMA = Arrow(TypedTerms.tm(TheoriesAsClasses.typedInstances(theory)), TypedTerms.tm(UnitType.unitType))
               val check = solver.check(Typing(stack, initfun, tp))
               if (!check)
                  return None
               // check that theory p exists, and is allowed to have instances
               // first check whether the theory exists
               val module = solver.getModule(theory.toMPath) match {
                  case None => return None
                  case Some(module: Theory) => module
               }
               val initialised  = check_initialised(solver,module,initfun).toSet // .map(x=>x.toPath)
               val open_definienses = get_uninitialised(module).toSet//.map(x => x.toPath)
               if(open_definienses != initialised )
                  return None
            }
            Some(TypedTerms.tm(TheoriesAsClasses.typedInstances(theory)))
         }
      }
   }
   def check_initialised(solver:Solver,theory : Theory,f : Term)(implicit stack: Stack, history: History): List[GlobalName] ={
      val result: List[GlobalName] = f match{
         case MutableVariables.assign(_,TheoriesAsClasses.field(_,OMID(name)),_) => {
            List(GlobalName(theory.path,name.name))
         }
         case SequencingOps.sequence(_,_,left,right) => check_initialised(solver,theory,left) ++ check_initialised(solver,theory,right)
         case IfThenElse.ifte(_,cond,ifB,elseB) => {
            // we could probably do something clever with the condition here
            // to legalise more constructors
            val ifBcheck = check_initialised(solver, theory,ifB)
            val elseBcheck = check_initialised(solver,theory,elseB)
            ifBcheck.intersect(elseBcheck)
         }
         case OMS(x) => solver.getDef(x) match{
            case Some(tX) => check_initialised(solver,theory,tX)
            case None => List()
         }
         case ComplexTerm(p, sub, con, args) =>
            args flatMap (x => check_initialised(solver, theory, x))
         // in the future we might want more cases here
         case otherwise => List()
      }
      result
   }
   def get_uninitialised(thy : Theory): List[GlobalName] ={
      thy.getConstants flatMap { x=>
         x.df match{
            case None => Some(GlobalName(thy.path,x.name))
            case Some(_) => None
         }
      }
   }
}

object FieldInstance extends InferenceRule(TheoriesAsClasses.field.path, OfType.path) {
   val instType = new RepresentedRealizedType(instanceMeta.anyInstance.term, InstanceType)

   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Option[Term] = {
      //
      tm match {
         case TheoriesAsClasses.field(v, OMS(field)) =>
            val inferred_theory = solver.inferType(v)
            inferred_theory match{
               /*case Some(TheoriesAsClasses.typedInstances(OMID(thy_type))) => {
                  // thy_type.module
                  val pth = thy_type.module ? field.toLocalName
                  val thy = solver.getType(pth)
                  thy
                  // None
               }*/
               case Some(OMA(Apply.term,List(TypedTerms.tm.term,TheoriesAsClasses.typedInstances(OMID(thy_type))))) => {
                  // thy_type.module
                  val pth = thy_type.module ? field.toLocalName
                  val thy = solver.getType(pth)
                  thy
                  // None
               }
               case _ => None
            }
         // throw GetError(tm.toMPath, " right branch with object " + theory.toString+ " and field "+ name.toString)
         //solver.getType(inst.theory.path ? field.toLocalName)
         //inst.theory.getO(field.name) match {
         //   case None => None
         //  case Some(tm:Constant) =>tm.tp
         // }
         case OMA(f,xs) =>
            throw GetError(tm.toMPath, " OMA in field "+tm.toString+ " " + f.toString + " xs " + xs.toString)
         case _=> throw GetError(tm.toMPath, " wrong branch in field "+tm.toString+ " " + tm.getClass.toString)
            None
      }
   }
}

object tmVariance extends VarianceRule(TypedTerms.tm.path){
   /**
    * pre all arguments covered
    *
    * @return Some(b) if the judgment was proved/disproved, None if the result is inconclusive
    */
   override def apply(solver: Solver)(tp1: Term, tp2: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
      val TypedTerms.tm(a) = tp1
      val TypedTerms.tm(b) = tp2
      a match {
         case EmptyType.void.term => Some(true)
         case theory => ???//...//solver.check(Subtyping())
         case _ => None
      }
   }
}

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
