package latin2.proving

import info.kwarc.mmt.api.objects.{OML, OMV, Term, Typing}
import lf.{Implication, Proofs, Tactics, TacticsLF, TypedTerms, TypedUniversalQuantification, Types}
import info.kwarc.mmt.api._
import objects._
import checking._
import info.kwarc.mmt.api.symbols.OMLReplacer
import info.kwarc.mmt.lf._

/*
object CheckProof extends TypingRule(TacticsLF.proofLF.path, OfType.path) {

} */
/*
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
} */