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


case class ExecutionError(tm : Term) extends Exception

/**
 * Builds a new instance of a theory
 * Currently, we only perform static checks during typechecking, but this
 * may need to be strictified using checks in check_fully_initialised
 * In that case we throw an ExecutionError, which may be caught by an MMT try-catch block
 */
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
    // TODO: add an actual runtime check if necessary
    true
  }
}

/**
 * Accesses a field (i.e. constant) in an instantiated theory.
 * FieldRun is guaranteed to return a value everywhere aside from the initializer
 */
object FieldRun extends ExecutionRule(TheoriesAsClasses.field.path){
  override def under = List() // Apply.path
  val instType = new RepresentedRealizedType(instanceMeta.anyInstance.term, InstanceType)

  def apply(controller:Controller, callback: ExecutionCallback, env: RuntimeEnvironment, prog: Term) : Term = {
    prog match {
      case TheoriesAsClasses.field(obj,OML(name,_,_,_,_)) =>
        val objE = callback.execute(obj)
        objE match{
          case TheoriesAsClasses.typedInstance(instType(inst))=>
            inst.get(GlobalName(inst.theory.path,name)).get
        }
      // this should always exist, since it typechecks
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
      case MutableVariables.assign(_,TheoriesAsClasses.field(_,OML(name,_,_,_,_)),_) => {
        List(GlobalName(theory.path,name))
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
      case TheoriesAsClasses.field(v, OML(name,_,_,_,_)) =>
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
            val pth = thy_type.module ? name//field.toLocalName
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
