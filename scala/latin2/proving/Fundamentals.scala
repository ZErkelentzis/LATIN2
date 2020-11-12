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

/** starts an [[ImperativeProver]] when checking a term of the form proof(steps) */
object CheckProof extends InferenceAndTypingRule(PropositionsITP.proof.path, OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val PropositionsITP.proof(steps) = tm
    val tp = tpO.getOrElse(return (None,None)) // for now we only use this as a checking rule, but inference is also possible
    var goal = ProofGoal(stack, tp, history + "starting prover")
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover = new ImperativeProver(solver, rules, goal)
 //   Solver.breakAfter(350)
    steps.foreach {step =>
      // history += step.head.name
      val r = prover.makeStep(step)
      if (!r) {
        solver.error("proof step application failed: " + solver.presentObj(step))(prover.currentHistory)
        return (None,Some(false))
      }
    }
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

/** runs an imperative proof by executing steps while maintaining a list of open goals
  * @param rules the rules for all steps
  * @param initGoal the initial goal
  */
class ImperativeProver(val solver: Solver, rules: List[ProofStepRule], initGoal: ProofGoal) {
  private def initContext = initGoal.stack.context
  // the proof state: the list of open goals
  private var goals: List[ProofGoal] = List(initGoal)

  implicit def currentHistory = goals.head.history

  /** the current proof state */
  def getGoals = goals
  /** done if all no open goals left */
  def isSolved = goals.isEmpty

  /**
    * applies one step to the first open goal, new open goals are added to the beginning
    * @return true if the step was applied successfully
    */
  def makeStep(step: Term): Boolean = {
    val currentGoal = goals.head
    val stepRule = rules.find(_.applicable(step)).getOrElse(return solver.error("no applicable rule"))
    val newGoalsO = stepRule(this, currentGoal, step)
    newGoalsO match {
      case Some(newGoals) =>
        goals = newGoals ::: goals.tail
      case None =>
        return solver.error("step failed")
    }
    true
  }

  /** awkward, but necessary for now: all terms in the proof that were entered by the user must be cleaned like this before using them in the proof */
  def clean(stack: Stack, tm: Term) = {
    val localExtension: Context = stack.context.drop(initContext.length)
    OMLReplacer(localExtension.id)(tm, initContext)
  }
}

/** a rule for applying a proof step in an [[ImperativeProver]] */
abstract class ProofStepRule(val head: GlobalName) extends SingleTermBasedCheckingRule {
  /**
    * @return the list of goals that replace the input goal, None if failure
    */
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]]
}

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

object UseStep extends ProofStepRule(PropositionsITP.use.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val PropositionsITP.use(p) = step
    val pC = prover.clean(goal.stack, p)
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term")
    Some(Nil)
  }
}


