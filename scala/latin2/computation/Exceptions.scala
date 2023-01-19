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

case class MMTException(tm : Term) extends Exception
/**
 * Throws an MMT exception by throwing a Scala "MMTException"
 * In conjunction with TryCatchRun this forms a direct embedding of MMT exception as Scala exceptions
 */
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
/**
 * Catches an MMT exception by executing the "handler" in case an exception is caught.
 * This can also catch "ExecutionErrors" that occur as part of the instantiation of New theory-as-classes instances
 * In conjunction with TryCatchRun this forms a direct embedding of MMT exception as Scala exceptions
 */
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

