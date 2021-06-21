package latin2.proving

import info.kwarc.mmt.api.objects.{OML, OMV, Term, Typing}
// import lf.{Implication, Proofs, Tactics, TacticsLF, TypedTerms, TypedUniversalQuantification, Types}
import info.kwarc.mmt.api._
import objects._
import checking._
import info.kwarc.mmt.api.symbols.OMLReplacer
import info.kwarc.mmt.api.uom.ConstantScala
import info.kwarc.mmt.lf._


/*
case class LambdaTree(ns : List[LambdaTreeNode] , holes : List[Int])
abstract class LambdaTreeNode
case class LambdaHole( g : Goal) extends LambdaTreeNode
case class LambdaTermNode(c : ConstantScala  ) extends LambdaTreeNode



object CheckProof extends InferenceRule(TacticsLF.proofLF.path, OfType.path) {
  def apply(solver: Solver, tm: Term, covered: Boolean)(implicit stack: Stack, history: History): Option[Term] = {
    val TacticsLF.proofLF(trm, steps) = tm
    val rules = solver.rules.getOrdered(classOf[ProofStepRuleLF])
    val pm = new ProofMachine(solver , steps , rules  )
    pm.executeProof(steps , ProofState( List(Goal(trm , stack))  ,None , history)) match {
      case ProofState(_ , res  , h) => {
        res
      }
      case _ => None
    }
  }
}


class ProofMachine(solver : Solver , steps : List[Term]  , rules : List[ProofStepRuleLF]  /* , initCtx : Context */) {
//  private def initContext = initCtx


  def clean(stack: Stack, tm: Term) = {
    // val localExtension: Context = stack.context.drop(stack.length)
    OMLReplacer(stack.context.id)(tm, Context())
  }
  def executeProof(stps : List[Term] ,ps : ProofState): ProofState = stps match {
    case Nil => ps
    case (x :: xs) => {
      val apRule = rules.find(_.applicable(x)).get

    }
  }
}

case class ProofState(lt: LambdaTree , history : History)

case class Goal(goal : Term , ctx : Stack , hn : Int )

abstract class ProofStepRuleLF(val head: GlobalName) extends SingleTermBasedCheckingRule {
  /**
   * @return the list of goals that replace the input goal, None if failure
   */
  def apply(prover: ProofMachine, proofState : ProofState): Either[ProofState, (ProofState, String)]
}


object PrintProofStateTactic extends  ProofStepRuleLF(TacticsLF.ppsLF.path){
  def apply(prover: ProofMachine, ps : ProofState ): Either[ProofState, (ProofState, String)] = {
    prover.solver.report("proofstate" , ">>>>>>>>>>>> PROVING: " + prover.solver.checkingUnit.component.toString + " <<<<<<<<<<<<<")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  prettyPrintHyps(prover.solver ,goal.stack))
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  prover.solver.presentObj(goal.tp))
    prover.solver.report("proofstate" , "-----------END----------")
    Left(ps)
  }
}
*/