package latin2.proving

import latin2.proving._
import lf.{Implication, Proofs, Tactics, Types}
import info.kwarc.mmt.api._
import info.kwarc.mmt.lf.{Arrow, Pi}
import objects._



object VoidTactic extends ProofStepRule(Tactics.void.path){
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    step match {
      case Tactics.void(ls) => {
        Some(List(goal))
      }
    }
  }
}


object PrintProofStateTactic extends  ProofStepRule(Tactics.pps.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  goal.stack.toString)
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  goal.tp.toString)
    prover.solver.report("proofstate" , "-----------END----------")
    Some(Nil)
  }
}


// do a BackWarD step (i.e. apply an implication to a goal)

object BwdTactic extends ProofStepRule(Tactics.bwd.path){


  def getHead(tm : Term) : (List[Term] , Term) = {
    def getHeadL(tm: Term): (List[Term], Term) = tm match {
      case Implication.impl(h, t) => {
        val (ls, hd) = getHeadL(t)
        (h :: ls, hd)
      }
      case _ => (Nil, tm)
    }

    tm match {
      case Proofs.ded(v) => getHeadL(v)
    }

  }
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    step match {
      case Tactics.bwd(OMID(pt)) => {
        val nn = pt.name
        val tmp  = prover.solver.checkingUnit.context(nn).tp
        tmp match {
          case None =>{
            prover.solver.error("the used term has no type")(goal.history)
            None
          }
          case Some(tptp) => {
            val (t, h) = getHead(tptp)
            val Proofs.ded(v) = goal.tp
            prover.solver.check(Equality(goal.stack, h, v, Some(Types.tp.term)))(goal.history + "the conclusion of the backward step has to be equal to the goal")
            val newGoals = t.map(x => ProofGoal(goal.stack , Proofs.ded(x) , goal.history))
            Some(newGoals)
          }
        }
      }
    }
  }
}

object IgnoreTactic extends  ProofStepRule(Tactics.ignore.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    Some(Nil)
  }
}