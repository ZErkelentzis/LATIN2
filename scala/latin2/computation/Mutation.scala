package latin2.computation

import info.kwarc.mmt.api.{objects, _}
import objects.{Stack, _}
import info.kwarc.mmt.api.execution._
import info.kwarc.mmt.api.checking._
import info.kwarc.mmt.api.uom._
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.modules.Theory
import info.kwarc.mmt.api.symbols.Constant
import info.kwarc.mmt.lf._
import info.kwarc.mmt.lf.structuralfeatures.StructuralFeatureUtils.{NONE, getConstants}
import lf._

import scala.::



object AssignmentRun extends ExecutionRule(MutableVariables.assign.path){
  override def under = List(Apply.path)
  val instType = new RepresentedRealizedType(instanceMeta.anyInstance.term, InstanceType)

  def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term): Term={
    prog match{
      case MutableVariables.assign(tp,v1 : OMV,t2) =>
        val t2E = callback.execute(t2)
        env.stack.assign(v1.name, t2E)
        UnitType.unit
      case MutableVariables.assign(tp,TheoriesAsClasses.field(v,OML(nm,_,_,_,_)),t2)=>
        val vE = callback.execute(v)
        vE match{
          case TheoriesAsClasses.typedInstance(instType(inst)) =>inst.set(GlobalName(inst.theory.path,nm),t2)
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

