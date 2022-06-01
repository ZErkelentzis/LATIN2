package latin2.computation

import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.uom._
import info.kwarc.mmt.api.execution.{ExecutionRule,ExecutionCallback,RuntimeEnvironment, RulePreprocessor}
import info.kwarc.mmt.lf.LFConstantScala._
import info.kwarc.mmt.lf._
import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend.Controller
import objects._
import lf._
import info.kwarc.mmt.api.checking._
import info.kwarc.mmt.lf.Common.isTypeLike
import objects.Conversions._
import uom._
import info.kwarc.mmt.api.symbols.Constant


object PrintRun  extends ExecutionRule(CF.print.path) {
   override def under: List[GlobalName] =List(Apply.path)
   
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term = {
      prog match {
         case CF.print(c ,a ) =>
            val aE = callback.execute(a)
            println(controller.presenter.asString(aE))
            CF.unit
      }
   }
}



object DefinedRun extends RulePreprocessor(CF.define.path){
   override def under: List[GlobalName]= List(Apply.path)
   def apply(const : Constant) : ExecutionRule = {
      const.tp match {
         case Some(CF.define(tp,OMID(gname : GlobalName),target)) => {
            new DefinedRule(const.path, target)
         }
         // case _=> None
      }
   }
}



class DefinedRule(override val head: GlobalName, val targetTerm : Term) extends ExecutionRule(head){
   override def under: List[GlobalName]= List(Apply.path)
   override def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case ApplyGeneral(OMID(head), ls) => {
            // lazy evaluation to prevent infinite loops
            lazy val executed = ls map callback.execute
            ApplyGeneral(targetTerm,executed)
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
}
*/
object MinusRun extends ExecutionRule(CF.minus.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.minus(t1,t2) =>
            val t1E = callback.execute(t1)
            val t2E = callback.execute(t2)
            // t1E+t2E
            t1E match {
               case OMLIT(v1 : BigInt,rt1) => t2E match {
                  case OMLIT(v2 : BigInt,rt2) => {
                     if(v1 > v2) {
                        OMLIT(v1 - v2, rt1)
                     }
                     else {
                        OMLIT(BigInt(0),rt1)}
                  }
               }
            }
      }
   }
}

object IfteRun extends ExecutionRule(CF.ifte.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.ifte(tp,b,t1,t2) =>
            val cond = callback.execute(b)
            cond match {
               case CF._true(_) => callback.execute(t1)
               case CF._false(_) => callback.execute(t2)
            }
      }
   }
}

object GeRun extends ExecutionRule(CF.ge.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.ge(l,r) =>
            val lE = callback.execute(l)
            val rE = callback.execute(r)
            lE match {
               case OMLIT(v1 : BigInt,rt1) => rE match {
                  case OMLIT(v2 : BigInt,rt2) => {
                     if(v1 > v2)
                        CF._true
                     else CF._false
                  }
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
                        CF._true
                     else CF._false
                  }
               }
            }
      }
   }
}

object AssignmentRun extends ExecutionRule(CF.assign.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
      prog match{
         case CF.assign(tp,v1 :OMV,t2) =>
            val t2E = callback.execute(t2)
            env.stack.assign(v1.name, t2E)
            CF.unit
         case CF.assign(tp,n,t2) => ???
      }
   }
}


object DeclareRun extends ExecutionRule(CF.declare.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback:ExecutionCallback,env:RuntimeEnvironment,prog: Term):Term={
      prog match{
         case CF.declare(tp1,tp2,initVal, OMBINDC(term, con, scope::Nil)) => {
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

object SequenceRun extends ExecutionRule(CF.sequence.path){
   override def under = List(Apply.path)
   def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
      prog match {
         case CF.sequence(tp1,tp2,fst,snd) =>
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
