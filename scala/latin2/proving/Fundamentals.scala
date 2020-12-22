package latin2.proving

import info.kwarc.mmt.api._
import objects._
import checking._
import info.kwarc.mmt.api.symbols.OMLReplacer
import info.kwarc.mmt.lf._
import lf.PropositionsITP
import lf.Proofs
import lf.Types
import lf.TypedTerms
import lf.PLITP
import lf.SFOLITP
import lf.Implication
import lf.TypedUniversalQuantification

import scala.collection.mutable.ListBuffer

/** starts an [[ImperativeProver]] when checking a term of the form proof(steps) */
object CheckProof extends InferenceAndTypingRule(PropositionsITP.proof.path, OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val PropositionsITP.proof(steps) = tm
    val tp = tpO.getOrElse(return (None,None)) // for now we only use this as a checking rule, but inference is also possible
    var goal = ProofGoal(stack, tp, history + "starting prover")
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover : ImperativeProver = new ImperativeProver(goal , rules,  solver)

 //   Solver.breakAfter(350)
    if (prover.isSolved)
    {
      solver.report("proofstate" , "proof succeeded: " + solver.checkingUnit.component.toString ) ; (tpO,Some(true))
    } else
    {
      solver.report("proofstate" , "proof failed: " +  solver.checkingUnit.component.toString)  ; (tpO,None)
    }

  }
}



/** proof goal in an [[ImperativeProver]]
  * @param stack the context of the goal, including local extensions
  * @param tp the type to prove
  * @param history for logging
  */
case class ProofGoal(stack: Stack, tp: Term, history: History)


/*

class ProofMachine(concreteProver: ConcreteProver) {
  var concp : ConcreteProver = concreteProver
  def toIp = concreteProver.asInstanceOf[ImperativeProver]
}
*/

abstract class ConcreteProver( initGoal: ProofGoal , val rules: List[ProofStepRule] , val solver: Solver){
  var makeStep :  Term =>  Boolean
  var redoStep : () => Boolean
  var undoStep : () => Boolean
}


// case class LambdaGoal(Goal : OMV  , Hyps : List[OMV])

class ImperativeProver( initGoal: ProofGoal,  val rules: List[ProofStepRule],val solver: Solver)  {
  private def initContext = initGoal.stack.context
  // the proof state: the list of open goals
  protected var goals: List[ProofGoal] = List(initGoal)

  implicit def currentHistory = goals.head.history

  /** the current proof state */
  def getGoals = goals
  /** done if all no open goals left */
  def isSolved = goals.isEmpty

  def clearGoals = {goals = Nil}

  def setGoals(gls : List[ProofGoal]) = {goals = gls  }


  var lambdaProofTerm : Term = OMV(Context.pickFresh(solver.checkingUnit.context ++ initGoal.stack.context,  LocalName("!!"))._1)

  var lambdaGoals : List[OMV]  = List(lambdaProofTerm.asInstanceOf[OMV])

//  var lambdaGoals : List[LambdaGoal]  = List(LambdaGoal(lambdaProofTerm.asInstanceOf[OMV] , List())   )

  var stepHistory : List[Term] = Nil

  var toDoSteps : List[Term] = Nil

  var goalsHistory : List[List[ProofGoal]] = Nil

  var lambdaGoalsHistory : List[List[OMV]] = List(lambdaGoals)

//  var calcLambdaGoalsHistory : List[List[Int]] = Nil

  var lambdaTermHistory : List[Term] = List(lambdaProofTerm)

  var errorstate : Boolean = false

//  var makeStep : Term => Boolean = makeStepConcrete
//  var redoStep : () =>  Boolean = redoStepConcrete
//  var undoStep : () => Boolean = undoStepConcrete

  def lambdaGoalsToContext : Context = {
    var res = Context()
    for (i <- lambdaGoals){
      res = res ++ VarDecl(i.name)
    }
    res
  }


  /**
    * applies one step to the first open goal, new open goals are added to the beginning
    * @return true if the step was applied successfully
    * */

  def executeProof(stps : List[Term]): Unit ={
    stps.foreach {step =>
      // history += step.head.name
      makeStep(step)
      if (errorstate) {
        solver.error("proof step application failed: " + solver.presentObj(step))(currentHistory)
      }
    }
  }

  def makeErrorStep(step : Term) = {
    errorstate = true
    stepHistory = step ::  stepHistory
  }

  def undoErrorStep() ={
    errorstate = false
    toDoSteps = stepHistory.head :: toDoSteps
    stepHistory = stepHistory.tail

  }
/*
  def makeStep(step : Term): Unit = {
    if (errorstate) return
    val stepRule = rules.find(_.applicable(step)).getOrElse({solver.error("no applicable rule"); makeErrorStep(step) ; return})
    stepRule.isInstanceOf[SimpleProofStepRule] match {
      case true => {
        val sStepRule = stepRule.asInstanceOf[SimpleProofStepRule]
        val (gls , lt , lgls) = sStepRule(step , goals.head , this).getOrElse({makeErrorStep(step) ; return})

       // val newLam = Lambda( lt)

        stepHistory = step ::  stepHistory
        goalsHistory = goals :: goalsHistory
        goals =  gls ++ goals.tail
        val lg = lambdaGoals.head
        val sb = Substitution(Sub( lg.name , lt ))
        lambdaTermHistory = lambdaProofTerm :: lambdaTermHistory
        lambdaProofTerm = PlainSubstitutionApplier(lambdaProofTerm , sb)
        lambdaGoalsHistory = lambdaGoals :: lambdaGoalsHistory
        lambdaGoals =  lgls ++ lambdaGoals.tail

      }
      case false => {
        val cStepRule = stepRule.asInstanceOf[ComplexProofStepRule]
        cStepRule(step , this)

      }
    }
  }
*/
  def makeStep(step : Term): Unit = {
    if (errorstate) return
    val stepRule = rules.find(_.applicable(step)).getOrElse({solver.error("no applicable rule"); makeErrorStep(step) ; return})
    stepRule  match {
      case sStepRule : SimpleProofStepRule  => {
        val (gls , lt , lgls) =  sStepRule(step , goals.head , this).getOrElse({makeErrorStep(step) ; return})


        stepHistory = step ::  stepHistory
        goalsHistory = goals :: goalsHistory
        goals =  gls ++ goals.tail
        val lg = lambdaGoals.head
        val sb = Substitution(Sub( lg.name , lt ))
        lambdaTermHistory = lambdaProofTerm :: lambdaTermHistory
        lambdaProofTerm = SmartSubstitutionApplier(lambdaProofTerm , sb)
        lambdaGoalsHistory = lambdaGoals :: lambdaGoalsHistory
        lambdaGoals =  lgls ++ lambdaGoals.tail

      }

      case cStepRule : ComplexProofStepRule => {
        cStepRule(step , this)

      }
    }
  }

  def redoStep(): Unit ={
    toDoSteps match {
      case Nil =>
      case x :: xs => {
        toDoSteps = toDoSteps.tail
        makeStep(x)
      }
    }
  }


  def makeUndoStep(step : Term): Unit = {
    val stepRule = rules.find(_.applicable(step)).getOrElse({solver.error("no applicable rule") ; errorstate= true ; return })
    stepRule.isInstanceOf[SimpleProofStepRule] match {
      case true => {
        toDoSteps = stepHistory.head :: toDoSteps
        stepHistory = stepHistory.tail
        goals = goalsHistory.head
        goalsHistory =  goalsHistory.tail
        lambdaProofTerm = lambdaTermHistory.head
        lambdaTermHistory = lambdaTermHistory.tail
        lambdaGoals = lambdaGoalsHistory.head
        lambdaGoalsHistory = lambdaGoalsHistory.tail

      }
      case false => {
        val cStepRule = stepRule.asInstanceOf[ComplexProofStepRule]
        cStepRule.undoStep(step, this)

      }
    }
    errorstate = false
  }

  def undoStep(): Unit = {
    if (errorstate) {undoErrorStep() ; return}
    stepHistory match {
      case Nil =>
      case x :: xs => {
        val trm = stepHistory.head
        makeUndoStep(trm)
      }
    }
  }
/*
  def makeStep(step: Term): Boolean = {
    val currentGoal = goals.head
    val stepRule = rules.find(_.applicable(step)).getOrElse(return solver.error("no applicable rule"))


    val newGoalsO = stepRule(this, currentGoal, step)
    newGoalsO match {
      case Some(newGoals) =>
        goals = newGoals ::: (if (goals.isEmpty) Nil else  goals.tail)
      case None =>
        return solver.error("step failed")
    }
    true
  }
*/
  /** awkward, but necessary for now: all terms in the proof that were entered by the user must be cleaned like this before using them in the proof */
  def clean(stack: Stack, tm: Term) = {
    val localExtension: Context = stack.context.drop(initContext.length)
    OMLReplacer(localExtension.id)(tm, initContext)
  }

/*
  def executeSteps(steps : List[Term]) : Boolean = {
    steps.foreach {step =>
      // history += step.head.name
      val r = makeStep(step)
      if (!r) {
        solver.error("proof step application failed: " + solver.presentObj(step))(currentHistory)
        return false
      }
    }
    true
  }


  def nextStep(t : Term) : Boolean = {
    stepHistory = t :: stepHistory
    goalHistory = goals :: goalHistory
    val r = makeStep(t)

 //   lambdaProofTermHistory = lambdaProofTerm :: lambdaProofTermHistory
   // lambdaGoalsHistory = lambdaGoals :: lambdaGoalsHistory
    if(!r){
      solver.error("proof step application failed: " + solver.presentObj(t))(currentHistory)
      return false
    }
    true
  }

  def nextStepEmptyToDo(t : Term) : Boolean = toDoSteps.isEmpty match {
    case false => false
    case true => {
      nextStep(t)
    }
  }


  def nextStep() : Boolean = {
    val t = toDoSteps.head
    toDoSteps = toDoSteps.tail
    val r = nextStep(t)
    if(!r){
      solver.error("proof step application failed: " + solver.presentObj(t))(currentHistory)
      return false
    }
    true
  }

  def nextStepPost(trm : Term) : Boolean = {

    val t = toDoSteps.head
    toDoSteps = toDoSteps.tail ++ List(trm)
    val r = makeStep(t)
    if(!r){
      solver.error("proof step application failed: " + solver.presentObj(t))(currentHistory)
      return false
    }
    true
  }

  def redoStep() : Boolean = {
    if (toDoSteps.isEmpty) return false
    val t = toDoSteps.head
    toDoSteps = toDoSteps.tail
    val r = nextStep(t)
    if(!r){
      solver.error("proof step application failed: " + solver.presentObj(t))(currentHistory)
      return false
    }
    true
  }

  def undoStep() : Unit = {
    if (stepHistory.isEmpty) return
    toDoSteps = stepHistory.head :: toDoSteps
    stepHistory = stepHistory.tail
    goals = goalHistory.head
    goalHistory = goalHistory.tail
 //   lambdaGoals = lambdaGoalsHistory.head
 //   lambdaGoalsHistory = lambdaGoalsHistory.tail
  //  for (i <- calcLambdaGoalsHistory.head ){
 //     lambdaGoals(i).v = HoleNode()
 //   }
 //   calcLambdaGoalsHistory = calcLambdaGoalsHistory.tail
  }

  def undoDeleteStep() : Unit = {

  }

  def startNewProof: Unit = {

  }
*/
}




abstract class ProofStepRule extends SingleTermBasedCheckingRule

/*
/** a rule for applying a proof step in an [[ImperativeProver]] */
abstract class ProofStepRule(val head: GlobalName) extends SingleTermBasedCheckingRule {
  /**
    * @return the list of goals that replace the input goal, None if failure
    */
 // def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]]
  // def apply(prover: ImperativeProver, step : Term)
  abstract def apply
}
*/

abstract class SimpleProofStepRule(val head : GlobalName) extends ProofStepRule {
  def apply (t : Term , g : ProofGoal , ip : ImperativeProver): Option[(List[ProofGoal] /*new goal in lambda */, Term /* new part of lambdaterm */ , List[OMV])]

}
/*
abstract class SemiComplexProofStepRule(val head : GlobalName) extends ProofStepRule {
  def apply (t : Term , g : ProofGoal , ip : ImperativeProver): Option[(List[(ProofGoal ,OMV /*new goals in lambda */)], Term /* new part of lambdaterm */  )]

}

 */

abstract class ComplexProofStepRule(val head : GlobalName) extends ProofStepRule {
  def apply (t : Term , ip : ImperativeProver): Unit

  def undoStep(t : Term , ip : ImperativeProver) : Unit
}

/*
object AssumeStep extends ProofStepRule(PLITP.assume.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val PLITP.assume(OML(n,tO,_,_,_)) = step
    goal.tp match {
      case Proofs.ded(Implication.impl(f,g)) =>
        val df = Proofs.ded(f)
        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, df, Some(OMS(Typed.ktype))))(goal.history + "assumption must equal implicant")
        }
        val pg = ProofGoal(goal.stack ++ OMV(n) % df, Proofs.ded(g), goal.history + "assume")
        Some(List(pg))
      case tp =>
        prover.solver.error("only applicable to implication goal, found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }
}
*/
/*
object FixStep extends ProofStepRule(SFOLITP.fix.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val SFOLITP.fix(OML(n,tO,_,_,_)) = step
    goal.tp match {
      case Proofs.ded(TypedUniversalQuantification.forall(tp, body)) =>
        val ntp = TypedTerms.tm(tp)
        val stackN = goal.stack ++ OMV(n) % ntp
        val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, tp, Some(Types.tp.term)))(goal.history + "fix must equal quantification domain")
        }
        val pg = ProofGoal(stackN, Proofs.ded(bodyN), goal.history + "fix")
        Some(List(pg))
      case tp =>
        prover.solver.error("only applicable to universally quantified goal: found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }
}
*/

/*
object UseStep extends ProofStepRule(PropositionsITP.use.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val PropositionsITP.use(p) = step
    val pC = prover.clean(goal.stack, p)
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term")
    Some(Nil)
  }
}

*/
