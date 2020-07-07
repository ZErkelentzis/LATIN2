package latin2.proving

import info.kwarc.mmt.api._
import objects._
import checking._
import info.kwarc.mmt.lf._

import lf.PropositionsITP
import lf.PLITP
import lf.SFOLITP

case class ProofGoal(context: Context, goal: Term)

abstract class ProofStepRule(op: GlobalName) extends SingleTermBasedCheckingRule {
  def apply(goal: ProofGoal, step: Term): List[ProofGoal]
}

object CheckProof extends InferenceAndTypingRule(PropositionsITP.proof.path, OfType.path) {
  def apply(solver: Solver)(tm: Term, tp: Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val PropositionsITP.proof(steps) = tm
    var goal = ProofGoal(stack.context,tp.get) // TODO: for now we assume we always have the expected type
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover = new ITProver(rules,goal)
    steps.foreach {step => prover.makeStep(step)}
    if (prover.isSolved) (tp,Some(true)) else (tp,None)
  }
}

class ITProver(rules: List[ProofStepRule], initGoal: ProofGoal) {
  private var goals: List[ProofGoal] = List(initGoal)
  def makeStep(step: Term) {
    val currentGoal = goals.head
    goals = goals.tail
    val stepRule = rules.find(_.applicable(step)).getOrElse(return)
    val newGoals = stepRule(currentGoal, step)
    goals = newGoals ::: goals
  }
  def isSolved = goals.isEmpty
}