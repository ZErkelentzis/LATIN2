package latin2.computation

import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom._
import info.kwarc.mmt.api.execution.{ExecutionCallback, ExecutionRule, RulePreprocessor, RuntimeEnvironment}
import info.kwarc.mmt.lf.LFConstantScala._
import info.kwarc.mmt.lf._
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend.Controller
import objects._
import lf._
import info.kwarc.mmt.api.checking._
import info.kwarc.mmt.api.ontology.MMTExtractor
import info.kwarc.mmt.lf.Common.isTypeLike
import objects.Conversions._
import uom._
import info.kwarc.mmt.api.symbols.Constant

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
            // execute children
            // only execute the downstream if we have every term (i.e. before that we only beta-reduce the term)
            // TODO: double check this for soundness bugs
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
         case Booleans.tt(_) => true
         case Booleans.ff(_) => false
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

object NewRule extends SyntaxDrivenRule{
   def apply(...){
      prog match{
         case OMPMOD(p, args) =>
         CF.instance(p)
      }
   }
}*/

object IfRun extends ExecutionRule(BooleanExtensionality.`if`.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case BooleanExtensionality.`if`(tp,b,t1,t2) =>
            val cond = callback.execute(b)
            cond match {
               case Booleans.tt(_) => callback.execute(t1)
               case Booleans.ff(_) => callback.execute(t2)
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
                     return Booleans.tt
                  }
                  return Booleans.ff
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

/*
object MkExceptionRun extends ExecutionRule(Exceptions.`throw`){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match {
         case Exceptions.`throw`(tp,tm) => {
            throw new MMTException(tm,tp)
         }
      }
   }
}*/

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
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case MutableVariables.assign(tp,v1 :OMV,t2) =>
            val t2E = callback.execute(t2)
            env.stack.assign(v1.name, t2E)
            UnitType.unit
         case MutableVariables.assign(tp,n,t2) => ???
      }
   }
}


object DeclareRun extends ExecutionRule(MutableVariables.declare.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback:ExecutionCallback,env:RuntimeEnvironment,prog: Term):Term={
      prog match{
         case MutableVariables.declare(tp1,tp2,initVal, OMBINDC(term, con, scope::Nil)) => {
            // val first_arg = OMV(localName)
            env.stack.newVariable(con.variables.head)
            env.stack.assign(con.variables.head.name,initVal)
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
/*
object DeclareTerm extends InferenceRule(CF.declare.path, OfType.path) {
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = {
      println(tm)
      tm match {
        case CF.declare(con, body)  =>
           val x = con.getDeclarations.head.name
           val a = con.getDeclarations.head.tp.get
           if (!covered) isTypeLike(solver,a)
           val (xn,sub) = Common.pickFresh(solver, x)
           solver.inferType(body ^? sub, covered)(stack ++ xn % a, history) flatMap {bT =>
              if (bT.freeVars contains xn) {
                 // usually an error, but xn may disappear later, especially when unknown in b are not solved yet
                 solver.error("type of Declare-scope has been inferred, but contains free variable " + xn + ": " + solver.presentObj(bT))
                 None
              } else {
                 Some(bT)
              }
           }
        case _ => None // should be impossible
      }
   }
}
*/
