package latin2.proving

import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.checking.{History, InferenceAndTypingRule, Solver}
import info.kwarc.mmt.api.objects.{Context, Equality, OMBINDC, OMID, OML, OMS, OMV, PlainSubstitutionApplier, Stack, Sub, Substitution, Term, Typing, VarDecl}
import info.kwarc.mmt.lf.{Apply, ApplySpine, Arrow, Lambda, OfType, Typed}
import lf.{Implication, ImplicationNDI, NewTactics, Proofs, PropositionsITP, TypedTerms, TypedUniversalQuantification, TypedUniversalQuantificationND, Types}

import scala.collection.mutable.ListBuffer



object AssumeTactic extends SimpleProofStepRule(NewTactics.assume.path) {
  def apply( step: Term ,  goal: ProofGoal, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case NewTactics.assume(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Proofs.ded(Implication.impl(f,g)) =>{
            val df = Proofs.ded(f)
            val freenm = helperFunctions.genFresh(nm , goal.stack.context ++ prover.solver.checkingUnit.context ++ prover.lambdaGoalsToContext )
            val pg = ProofGoal(goal.stack ++ OMV(freenm) % df, Proofs.ded(g), goal.history + "assume")
            val newFVar = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context ++ prover.lambdaGoalsToContext)
            val newLam =  ImplicationNDI.impI(df, g , Lambda(freenm , df , OMV(newFVar)))
            Some(List(pg) , newLam , List(OMV(newFVar)))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}


object UseTactic extends SimpleProofStepRule(NewTactics.use.path) {
  def apply(step: Term , goal : ProofGoal , prover: ImperativeProver) = {
    val NewTactics.use(p) = step
    val pC = prover.clean(goal.stack, p)
    prover.solver.check(Typing(goal.stack, pC, goal.tp))(goal.history + "check proof term") match {
      case true =>  Some((List() ,  pC , List()))
      case false => prover.solver.error("use needs a term that has exactly the type of the goal")(goal.history); None
    }

  }
}


object SubproofTactic extends ComplexProofStepRule(NewTactics.subproof.path) {
  def apply(step: Term , prover: ImperativeProver ) : Unit =  {
    val NewTactics.subproof(stps) = step
    prover.toDoSteps =  stps ++ prover.toDoSteps
    prover.stepHistory = step :: prover.stepHistory
  }

  //maybe introduce metainf
  def undoStep(t: Term, ip:  ImperativeProver): Unit = {
    val NewTactics.subproof(stps) = t
    ip.toDoSteps  = t :: ip.toDoSteps.drop(stps.length)
    ip.stepHistory = ip.stepHistory.tail

  }
}



object SubgoalTactic extends SimpleProofStepRule(NewTactics.subgoal.path) {
  def apply(step : Term , goal : ProofGoal , prover : ImperativeProver ) : Option[(List[ProofGoal], Term , List[OMV])] = {
    val NewTactics.subgoal(OML(h, None , None , _ , _) , trm) = step
    val newg = ProofGoal(goal.stack ++  OMV(h) % trm , goal.tp , goal.history + ("added hypothesis " + h.toString + ": " + prover.solver.presentObj(trm)))
    val subg = ProofGoal(goal.stack , trm , goal.history + ("added new subgoal " + prover.solver.presentObj(trm)))
    val newFVar = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext )
    val newFVar2 = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext ++ VarDecl(newFVar) )
    val lt : Term = Apply (Lambda( h, trm , OMV(newFVar) )   , OMV(newFVar2) )
    Some(List(subg , newg) , lt , List(OMV(newFVar), OMV(newFVar2)))
  }
}



object BwdTactic extends SimpleProofStepRule(NewTactics.bwd.path){


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
  def apply(step : Term , goal : ProofGoal ,  prover : ImperativeProver ) = {
    step match {
      case NewTactics.bwd(trm) => {
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

            //lambda term

            val numHoles = newGoals.length

            val holes : ListBuffer[LocalName] = ListBuffer()
            val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
            for (i <- 0 until numHoles){
              val hname = helperFunctions.genHoleName(ctx ++ Context(holes.map(ln => VarDecl(ln)) : _*))
              holes.insert(0 , hname)
            }
//applygeneral maybe
            val lterm = ApplySpine(trm , holes.map(x => OMV(x)) : _ *)

            //lambda term

            val tmpl = holes.map(x => OMV(x))
            Some((newGoals , lterm , tmpl.toList))
          }
        }
      }
    }
  }
}



object FwdTactic extends  SimpleProofStepRule(NewTactics.fwd.path) {
  def apply(step: Term , goal: ProofGoal , prover: ImperativeProver ): Option[(List[ProofGoal], Term , List[OMV])] = {
    val NewTactics.fwd(OML(h, None, None, _, _), hs) = step
    val tmp = try {
      goal.stack.context(h)
    } catch {
      case e => return None
    }

    def loop(t: Term, ls: List[Term]): Option[Term] = (t, ls) match {
      case (Proofs.ded(thm), Nil) => Some(Proofs.ded(thm))
      case (Proofs.ded(thm), ls) => loop(thm, ls)
      case (Implication.impl(hd, tl), x :: xs) => {
        val xC = prover.clean(goal.stack, helperFunctions.removeDed( x))
        val tp = helperFunctions.removeDed(prover.solver.inferType(xC, false)(goal.stack, goal.history).getOrElse(return None))
        prover.solver.check(Equality(goal.stack, tp, hd, Some(Types.tp.term)))(goal.history + "fwd implication") match {
          case true => {
            loop(tl, xs)
          }
          case false => None
        }
      }
      case (TypedUniversalQuantification.forall(v, bd), x :: xs) => {
        val xC = prover.clean(goal.stack, helperFunctions.removeDed( x))
        // currently the following line is not useful since TypedUniversalQunatification.forall can't take a a prop/type as quantified variable
        val tp = helperFunctions.removeDed(prover.solver.inferType(xC, false)(goal.stack, goal.history).getOrElse(return None))
        // forall doesn't take a tm T (where T can be replaced by any other type f.ex. tm X) but just a T
        val vtm = lf.TypedTerms.tm(v)
        prover.solver.check(Equality(goal.stack, tp, vtm, Some(Types.tp.term)))(goal.history + "fwd forall") match {
          case true => {
            //    val stackN = goal.stack ++ Context(xC)
            val bodyN = prover.solver.simplify(Apply(bd, xC))(goal.stack, goal.history)
            loop(bodyN, xs)
          }
          case false => None
        }
      }
      case (trm, _) => Some(Proofs.ded(trm))
    }

    val tmp0 = loop(tmp.tp.getOrElse(return None), hs)
    tmp0 match {
      case None => None
      case Some(a) => {
        val tmp2 = goal.stack.context.variables.filter(p => p.name != h)
        val newCtx = Stack(Context(tmp2: _*)) ++ OMV(h) % a
        //       Some(List(ProofGoal(newCtx, goal.tp, goal.history + "fwd step done")))
        //      val newCtx = Stack(goal.stack.context ++ OMV(h) % a)

        //lambdaterm
        val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
        val newG = OMV(helperFunctions.genHoleName(ctx))
        val lam = Apply (Lambda(h ,  a , newG ) , ApplySpine(OMV(h) , hs : _ *) )

        //lambdaterm

        Some((List(ProofGoal(newCtx, goal.tp, goal.history + "fwd step done")) , lam , List(newG) ) )
      }
    }
  }
}


object AddhTactic extends SimpleProofStepRule(NewTactics.addh.path){
  def apply(step : Term, goal : ProofGoal ,   prover : ImperativeProver ): Option[(List[ProofGoal], Term , List[OMV])] = {
    val NewTactics.addh(trm, nn) = step
    if (goal.stack.context.variables.exists(p => p.name == nn.name)) {return None }
    val trm0 = prover.clean(goal.stack  , trm)
    val tp = prover.solver.inferType(trm0 , false)(goal.stack , goal.history)
    val gls = List(ProofGoal(goal.stack ++ OMV(nn.name) % tp.get  , goal.tp , goal.history + ("addh: added hypothesis :" + prover.solver.presentObj(OMV(nn.name) % tp.get))))
    //lambdaterm

    val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
    val newG = helperFunctions.genHoleName(ctx)
    val lam = Lambda(nn.name , tp.get ,  OMV(newG))

    //lambdaterm
    Some((gls, lam , List(OMV(newG)) ))
  }
}



object FixTactic extends SimpleProofStepRule(NewTactics.fix.path) {
  def apply(step: Term , goal: ProofGoal ,  prover: ImperativeProver) = step match {
    case NewTactics.fix(OML(n, None, None, _, _)) => {
      goal.tp match {
        case Proofs.ded(TypedUniversalQuantification.forall(tp, body)) => {
          val ntp = TypedTerms.tm(tp)
          val stackN = goal.stack ++ OMV(n) % ntp
          val bodyN = prover.solver.simplify(Apply(body, OMV(n)))(stackN, goal.history)
          val pg = ProofGoal(stackN, Proofs.ded(bodyN), goal.history + "fix")
          // lambda


          val ctx = prover.solver.checkingUnit.context ++ goal.stack.context  ++ prover.lambdaGoalsToContext
          val newG = helperFunctions.genHoleName(ctx)
          val lam = TypedUniversalQuantificationND.forallI( tp , bodyN , Lambda(n , ntp ,  OMV(newG)) )

          //lambda

          Some(List(pg) , lam , List(OMV(newG)))
        }
      }
    }
    case _ => prover.solver.error("fix has not the right form: " + step.toString())(goal.history); None
  }
}



object AssumelfxTactic extends SimpleProofStepRule(NewTactics.assumelfx.path) {
  def apply( step: Term ,  goal: ProofGoal, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case NewTactics.assumelfx(OML(nm , None , None , _  , _ )) => {
        goal.tp match {
          case Arrow(df,g) =>{
            val freenm = helperFunctions.genFresh(nm , goal.stack.context ++ prover.solver.checkingUnit.context ++ prover.lambdaGoalsToContext )
            val pg = ProofGoal(goal.stack ++ OMV(freenm) % df, g, goal.history + "assumelfx")
            val newFVar = helperFunctions.genHoleName(prover.solver.checkingUnit.context ++ goal.stack.context ++ prover.lambdaGoalsToContext)
            val newLam =  Lambda(freenm , df , OMV(newFVar))
            Some(List(pg) , newLam , List(OMV(newFVar)))
          }
        }
      }
      case _ => prover.solver.error("assume has not the right form")(goal.history) ; None
    }
  }
}



object theoremLFTactic extends InferenceAndTypingRule(NewTactics.theoremLF.path, OfType.path) {
  def apply(solver: Solver, tm: Term , tpD : Option[Term], covered: Boolean)(implicit stack: Stack, history: History): (Option[Term] , Option[Boolean])= {
    val NewTactics.theoremLF(typN, prf) = tm
    val  PropositionsITP.proof(steps) = prf
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val interp = new InteractiveLFProver(solver , rules , ProofGoal(stack , typN, history + "starting lf prover"))
    interp.executeInteractiveProof(steps)
    tpD match {
      case None =>
      case Some(tptp) => solver.check(Typing(stack , interp.prover.lambdaProofTerm , tptp ))
    }
    (Some(interp.prover.lambdaProofTerm) , Some(true))
  }
}


object BuildTactic extends SimpleProofStepRule(NewTactics.build.path) {
  def apply( step: Term ,  goal: ProofGoal, prover: ImperativeProver): Option[(List[ProofGoal], Term  , List[OMV] )] = {
    step match {
      case NewTactics.build(t) => {
        val tp = prover.solver.inferType(t , false)(goal.stack , goal.history).getOrElse(return None)
        prover.solver.check(Equality(goal.stack, goal.tp , tp , None))(goal.history) match {
          case false => None
          case true => Some(List() , t , List())
        }
      }
      case _ => prover.solver.error("build has not the right form " + step.toString)(goal.history) ; None
    }
  }
}