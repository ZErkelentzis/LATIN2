package latin2.proving

import info.kwarc.mmt.api.objects.{Equality, OML, OMS, OMV, Term, Typing}
import info.kwarc.mmt.lf.{Apply, Typed}
import lf.{Implication, Proofs, Tactics2, TypedTerms, TypedUniversalQuantification, Types}


object AssumeTactic extends ProofStepRule(Tactics2.assume.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    step match {
      case Tactics2.assume(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Proofs.ded(Implication.impl(f,g)) =>{
            val df = Proofs.ded(f)
            val pg = ProofGoal(goal.stack ++ OMV(nm) % df, Proofs.ded(g), goal.history + "assume")
            Some(List(pg))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}



object UseTactic extends ProofStepRule(Tactics2.use.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = {
    val Tactics2.use(p) = step
    val pC = prover.clean(goal.stack, p)
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term")
    Some(Nil)
  }
}

/*
object FixTactic extends ProofStepRule(Tactics2.fix.path) {
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term) = step match {
    case Tactics2.fix(OML(n, None, None, _, _)) => {
      goal.tp match {
        case Proofs.ded(TypedUniversalQuantification.forall(tp, body)) => {
          val ntp = TypedTerms.tm(tp)
          val stackN = goal.stack ++ OMV(n) % ntp
          val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
        }
      }
      case _ => prover.solver.error("fix has not the right form: " + step.toString())(goal.history); None
*/
      /*   val Tactics2.fix(OML(n,tO,_,_,_)) = step
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
  }
}

*/
