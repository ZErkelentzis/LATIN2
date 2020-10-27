package latin2.proving

import info.kwarc.mmt.api.objects.{OML, OMV, Term, Typing}
import lf.Tactics

import info.kwarc.mmt.api._
import objects._
import checking._
import info.kwarc.mmt.api.symbols.OMLReplacer
import info.kwarc.mmt.lf._


import lf.Proofs
import lf.Types
import lf.TypedTerms

import lf.Implication
import lf.TypedUniversalQuantification

/** starts an [[ImperativeProver]] when checking a term of the form proof(steps) */
object CheckProofTactic extends InferenceAndTypingRule(Tactics.prooft.path, OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val Tactics.prooft(steps) = tm
    solver.report("itptest" ,"!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
    val tp = tpO.getOrElse(return (None,None)) // for now we only use this as a checking rule, but inference is also possible
    var goal = ProofGoal(stack, tp, history + "starting prover")
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover = new ImperativeProver(solver, rules, goal)
    steps.foreach {step =>
      val r = prover.makeStep(step)
      if (!r) {
        solver.error("proof step application failed: " + solver.presentObj(step))(prover.currentHistory)
        return (None,Some(false))
      }
    }
    if (prover.isSolved) (tpO,Some(true)) else (tpO,None)
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


object AssumeTactic extends ProofStepRule(Tactics.assumet.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.assumet(OML(n,tO,_,_,_)) = step
    goal.tp match {
      case Arrow(hd,tl) =>

        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, hd , Some(OMS(Typed.ktype))))(goal.history + "assumption must equal implicant")
        }
        val pg = ProofGoal(goal.stack ++ OMV(n) % hd, tl , goal.history + "assume")
        Some(List(pg))
      case tp =>
        prover.solver.error("only applicable to implication goal, found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }
}




object FixTactic extends ProofStepRule(Tactics.fixt.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.fixt(OML(n,tO,_,_,_)) = step
    goal.tp match {
      case Pi(nm , typ , bd) =>
        val stackN = goal.stack ++ OMV(n) %  typ
        val bodyN = prover.solver.simplify(Apply(bd, OMV(nm)))(stackN, goal.history)
        tO.foreach {t =>
          val tC = prover.clean(goal.stack, t)
          prover.solver.check(Equality(goal.stack, tC, typ, Some(Types.tp.term)))(goal.history + "fix must equal quantification domain")
        }
        val pg = ProofGoal(stackN, bodyN, goal.history + "fix")
        Some(List(pg))
      case tp =>
        prover.solver.error("only applicable to universally quantified goal: found " + prover.solver.presentObj(tp))(goal.history)
        None
    }
  }
}

object UseTactic extends ProofStepRule(Tactics.uset.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics.uset(p) = step
    val pC = prover.clean(goal.stack, p)
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term")
    Some(Nil)
  }
}

