package latin2.proving

import latin2.proving._
import lf.{Implication, Proofs, Tactics, TypedUniversalQuantification, Types}
import info.kwarc.mmt.api._
import info.kwarc.mmt.lf.Apply
import info.kwarc.mmt.moduleexpressions.operators.typeops.LATIN2Environment.Logic.TypedTerms
import latin2.proving.helperFunctions.{NamedHypothesis, NamedOrUnnamedTerm, UnnamedHypothesis}
import objects._
import prettyprint._
import objects.OMV


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
    prover.solver.report("proofstate" , "-------- Proving: " + prover.solver.checkingUnit.component.toString + " ----------")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  prettyPrintHyps(prover.solver ,goal.stack))
    prover.solver.report("proofstate" , "GOAL---------------GOAL---------------GOAL")
    prover.solver.report("proofstate" ,  prover.solver.presentObj(goal.tp))
    prover.solver.report("proofstate" , "-----------END----------")
    Some(Nil)
  }
}

object PrintProofStateRawTactic extends  ProofStepRule(Tactics.ppsr.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    prover.solver.report("proofstate" , "-------- Proving: " + prover.solver.checkingUnit.component.toString + " ----------")
    prover.solver.report("proofstate" , "--------PROOF_STATE-------")
    prover.solver.report("proofstate" , "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS")
    prover.solver.report("proofstate" ,  printHypsRaw(goal.stack))
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
  /*    case Tactics.bwd(OMID(pt)) => {
        val pat = pt.toMPath
        val pat0 = pat.toGlobalName
        val tmp = try {
          prover.solver.inferType(OMS(pat0), true)(goal.stack, goal.history)
        } catch {
          case e => None
        }
        tmp match {
          case None => {
            prover.solver.error("the used term has no type")(goal.history)
            None
          }
          case Some(tptp) => {
            val (t, h) = getHead(tptp)
            val Proofs.ded(v) = goal.tp
            prover.solver.check(Equality(goal.stack, h, v, Some(Types.tp.term)))(goal.history + "the conclusion of the backward step has to be equal to the goal")
            val newGoals = t.map(x => ProofGoal(goal.stack, Proofs.ded(x), goal.history))
            Some(newGoals)
          }
        }
      } */
      case Tactics.bwd(trm) => {
        val trmC = prover.clean(goal.stack , trm)
        val tmp = prover.solver.inferType(trmC, false)(goal.stack, goal.history)
        tmp match {
          case None => {
            prover.solver.error("the used term has no type")(goal.history)
            None
          }
          case Some(tptp) => {
            val (t, h) = getHead(tptp)
            val Proofs.ded(v) = goal.tp
 //           val h0 = prover.clean(goal.stack , h)
            prover.solver.check(Equality(goal.stack, h, v, Some(Types.tp.term)))(goal.history + "the conclusion of the backward step has to be equal to the goal")
            val newGoals = t.map(x => ProofGoal(goal.stack, Proofs.ded(x), goal.history + ("applied bwd with " + prover.solver.presentObj(trm)) ))
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

object build {

}

// used inside build
object hole {

}

object FwdTactic extends  ProofStepRule(Tactics.fwd.path){
  def apply(prover: ImperativeProver, goal: ProofGoal, step: Term): Option[List[ProofGoal]] = {
    val Tactics.fwd(OML(h , None , None , _ , _) , hs) = step
    val tmp = try {goal.stack.context(h)} catch {case e  => return None}

    def loop(t : Term , ls : List[Term]) : Option[Term] = (t,ls) match{
      case (Proofs.ded(thm), Nil) => Some(Proofs.ded(thm))
      case (Proofs.ded(thm) , ls) => loop(thm , ls)
      case (Implication.impl(hd,t) , x::xs ) => {
        val tp = prover.solver.inferType(x , false)(goal.stack , goal.history).getOrElse(return None)
        val tC = prover.clean(goal.stack, tp)
        prover.solver.check(Equality(goal.stack, tC, hd, Some(Types.tp.term)))(goal.history + "fwd implication") match {
          case true => {
            loop(t , xs)
          }
          case false => None
        }
      }
      case (TypedUniversalQuantification.forall(typ, bd) , x::xs) => {
        val tpp = TypedTerms.tm(typ)
        val tC = prover.clean(goal.stack, x)
        val tp = prover.solver.inferType(tC , false)(goal.stack , goal.history).getOrElse(return None)
        prover.solver.check(Equality(goal.stack, tp , tpp , Some(Types.tp.term)))(goal.history + "fwd forall") match {
          case true => {
            val bdn = prover.solver.simplify(Apply(bd, x))(goal.stack, goal.history)
            loop(bdn , xs)
          }
          case false => None
        }
      }
      case (trm , _) => Some(Proofs.ded(trm))
    }

    val tmp0 = loop(tmp .tp.getOrElse(return None), hs)
    tmp0 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCtx = Stack(Context(tmp2 :_*))    ++ OMV(h) % a
        Some(List(ProofGoal(newCtx , goal.tp , goal.history + "fwd step done")))
      }
    }
  }



/*    val hyps = helperFunctions.getHyps(tmp.tp.getOrElse(return None))
    val tmp0 = hyps.map { case NamedHypothesis(ln, t) => t; case UnnamedHypothesis(t) => t }






    def loop(xs : List[Term] , ys : List[Term]) : Option[List[Term]] = (xs , ys) match{
      case (Nil , _) => Some(Nil)
      case (l :: ls , v :: vs ) => if (l == prover.solver.inferType(v , false)(goal.stack, goal.history).getOrElse(return None) ) {loop(ls , vs)} else {return None}
      case (ls , Nil) => Some(ls)
    }

  //  val tmp0 = helperFunctions.getNamedTerms(hs)
  //  val tmp1 =
    val conc = helperFunctions.getConclusion(tmp.tp.get)
    val tmp1 = loop(tmp0 , hs)
    tmp1 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCxt = Stack(Context(tmp2 :_*))    ++ OMV(h) % conc
        ProofGoal()
      }
    }
  } */
}

object printType {

}

object printDefinition {

}

object printLocation {

}

object SubgoalTactic extends ProofStepRule(Tactics.subgoal.path) {
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term) = {
    val Tactics.subgoal(OML(h, None , None , _ , _) , trm) = step
    val trmC = prover.clean(goal.stack ,  trm )
    val newg = ProofGoal(goal.stack ++  OMV(h) % trmC , goal.tp , goal.history + ("added hypothesis " + h.toString + ": " + prover.solver.presentObj(trm)))
    val subg = ProofGoal(goal.stack , trmC , goal.history + ("added new subgoal " + prover.solver.presentObj(trm)))
    Some(List( subg  ,  newg))
  }
}

//print the proof state (all branches)
object ppsa {

}

// add hypothesiss to proof context
object AddhTactic extends ProofStepRule(Tactics.addh.path){
  def apply(prover : ImperativeProver , goal : ProofGoal , step : Term): Option[List[ProofGoal]] = {
    val Tactics.addh(trm, nn) = step
    if (goal.stack.context.variables.exists(p => p.name == nn.name)) {return None }
    val trm0 = prover.clean(goal.stack  , trm)
    val tp = prover.solver.inferType(trm0 , false)(goal.stack , goal.history)
    Some(List(ProofGoal(goal.stack ++ OMV(nn.name) % tp.get  , goal.tp , goal.history + ("addh: added hypothesis :" + prover.solver.presentObj(OMV(nn.name) % tp.get)))))
  }
}

object contradiction {

}

// used to change the currently focused subgoal to another subgoal
object switchGoalTactic {

}

