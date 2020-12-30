package latin2.proving

import info.kwarc.mmt.api.{CPath, LocalName}
import info.kwarc.mmt.api.checking.{CheckingUnit, Solver}
import info.kwarc.mmt.api.objects.{Context, OMA, OMAorAny, OMID, OML, OMSemiFormal, OMV, Stack, Substitution, Term, WFJudgement}
import info.kwarc.mmt.api.parser.ParseResult
import lf.{Implication, Proofs, TypedUniversalQuantification}
import info.kwarc.mmt.lf._
import latin2.proving.prettyprint.printHypsRaw

import scala.collection.mutable.ListBuffer

object helperFunctions {
/*
  abstract class NamedOrUnnamedTerm

  case class UnnamedHypothesis(t : Term) extends  NamedOrUnnamedTerm
  case class NamedHypothesis(ln : LocalName, t : Term) extends  NamedOrUnnamedTerm


  def deconstructImps(t : Term) : List[NamedOrUnnamedTerm] = t match {
    case Implication.impl(h ,tl) => {
      val tmp = deconstructImps(tl )
      UnnamedHypothesis(h) :: tmp
    }
    case TypedUniversalQuantification.forall(OML(nn, None, None, _, _), tl) => {
      val tmp = deconstructImps(tl)
      NamedHypothesis(nn , tl) :: tmp
    }
    case h => List()
  }

  def getHyps(t : Term) : List[NamedOrUnnamedTerm] = t match {
    case Proofs.ded(trm) => {
      deconstructImps(trm)
    }
  }


  def getNamedTerms(xs : List[Term]) : Option[List[NamedOrUnnamedTerm]] = xs match{
    case OML(nn , None , _ , _ , _) :: OML(_,_,_,_,_) :: zs => None
    case OML(nn , None , _ , _ , _) :: trm :: zs => {
      val tmp = getNamedTerms(zs)
      tmp match {
        case Some(res) => {
          Some(NamedHypothesis(nn, trm) :: res)
        }
        case None => None
      }
    }
  }



  def getConclusion(t : Term) : Term = {

    def loop(tt : Term) : Term = tt match {
      case Implication.impl(_ , c) => {
        loop(c)
      }
      case trm => trm
    }

    t match {
      case Proofs.ded(thm) => {
        loop(thm)
      }
      case trm => loop(trm)
    }
  }
/*
  def containsHole(t : Term): Boolean = t match{
    case OMID(holeBuild.path) => true
    case OMA(s , ls) =>{
      containsHole(s) || ls.foldRight(false)((x,y) => y || containsHole(x))
    }
    case _ => false
  }
*/

  def removeDed(t : Term) : Term = t match {
    case Proofs.ded(trm) => trm
    case _ => t
  }


  def simpleSubstitution (l : LocalName ,orig  : Term  , rep : Term) : Term  = orig match {
    case OMV(n) => if (n == l) {rep} else orig
    case OML(n , _ , _ , _ , _) => {
      if (n == l) {
        rep
      } else {
        orig
      }
    }
    case OMA(f , ags ) => {
      OMA(simpleSubstitution(l , f , rep) , ags.map(x => simpleSubstitution(l , x , rep)) )
    }
    case OMID(p) => {
      if (p.name == l ) {rep} else orig
    }
    case OMAorAny(f , ags ) => {
      OMA(simpleSubstitution(l , f , rep) , ags.map(x => simpleSubstitution(l , x , rep)) )
    }
    case _ => orig
  }

  def simpleSubstituteRw(orig : Term , l : Term , r : Term) : Term = (orig == l) match {
    case true => r
    case false => orig match {
      case OMA(f , ags) => OMA(simpleSubstituteRw(f , l , r) , ags.map(x => simpleSubstituteRw(x , l , r)))
      case _ => orig
    }
  }


  def isNumberTerm(t : Term) : Boolean = t match {
    case OMV(n) => n.toString.forall(c => c.isDigit)
    case OML(n , None , None , None , None) => n.toString.forall(c => c.isDigit)
    case _ => false
  }

  def applyTacticsToGoal(ip : ImperativeProver , g : ProofGoal , ts : List[Term] ) : Option[List[ProofGoal]] = ts match {
    case Nil => Some(List(g))
    case x::xs => {
      val r = ip.rules.find(v => v.applicable(x)).getOrElse(return None)
      r(ip , g , x) match {
        case None => None
        case Some(gg) => {
          val tmp = gg.map(ggg => applyTacticsToGoal(ip, ggg, xs))
          tmp.foldLeft[Option[List[ProofGoal]]](Some(Nil))((p , p0) => (p , p0) match {
            case (None , _) => None
            case (_ , None) => None
            case (Some(res) , Some(curr)) => Some(curr ++ res)
          } )
        }
      }
    }
  }


  def termToInt(t : Term) : Option[Int] = t match {
    case OML(n , _ , _ , _ , _) => try Some(n.toString.toInt) catch {case e => None}
    case OMV(n) => try Some(n.toString.toInt) catch {case e => None}
    case OMSemiFormal(ls) => try Some(ls.head.freeVars.head.toString.toInt) catch {case e => None}
  }

  def replaceTermInTerm(rep : Term  , orig : Term) : Term = (orig == rep) match {
    case true => rep
    case false  => orig match {
      case OMA(f , args) => {
        OMA(replaceTermInTerm(rep , f)  , args.map(x => replaceTermInTerm(rep, x))  )
      }
      case _ => orig
    }
  }


  def containsTerm( searchTerm : Term ,  searchedTerm : Term) : Boolean = (searchTerm == searchedTerm) match {
    case true => true
    case false => searchedTerm match {
      case OMA(f , ags) =>  containsTerm(searchTerm , f) || ags.foldLeft(false) ((b , t) => b || containsTerm(searchTerm , t))
      case _ => false
    }
  }

/*
  def unify(t : Term , t0 : Term , vars : Term => List[OMV]) : Term  = {

    var freeTVars = vars(t)
    var freeT0Vars = vars(t0)
    var allVars = freeTVars.union(freeT0Vars)
    var sol : ListBuffer[(LocalName , Term)] = ListBuffer.empty


//    def eraseArgs(args : List[Term] , args0 : List[Term]):  = {

//    }

//    def genLambda()


    def unifyFreeFN(t : OMA , t0 : OMA) : Boolean = (t , t0) match {
      case (OMA(f, args), OMA(f0, args0)) =>  (allVars.contains(f) , allVars.contains(f0)) match{
        case (true , false) => args.head match {
          case OMV(ln) => {
            val tmp : (LocalName , Term) =  (ln , Lambda(Context() , replaceTermInTerm(OMV(ln) , OMA(f0 , args0))))
            sol += tmp
            true
          }
          case _ => false

        }
        case (false , true) => {
          unifyFreeFN(t0 , t)
        }
        case (true , true ) => {
          false
        }
      }
    }
/*
    def unifyFN(t : OMA , t0 : OMA) : Boolean = (t , t0) match {
      case (p @ OMA(f , args ) , p0 @ OMA(f0 , args0)) => (allVars.contains(f) , allVars.contains(f0)) match {
        case (true , _) | (_ , true) =>unifyFreeFN(p , p0)
        case (false , false) => (f == f0  && args.length == args0.length) match{
          case false => false
          case true => {

          }
        }
      }
    }

    def loop(nt : Term , nt0 : Term): Boolean = (allVars.isEmpty) match {
      case true => {
        true
      }
      case false => (nt , nt0) match {
        case (p : OMA , p0 : OMA ) => unifyFN(p , p0)
      }

    }

*/
    val bla : OMA = t.asInstanceOf[OMA]
    val bla0 : OMA = t0.asInstanceOf[OMA]
    val tmpp = unifyFreeFN(bla , bla0)
    if (tmpp) t else t0

  }

// deep copying a term
  def termCopyt(t : Term): Term = {

  }

  def copyGoals(gls : List[ProofGoal]) : List[ProofGoal] = gls match {
    case Nil => Nil
    case (ProofGoal(a,b,c))::xs =>

  }

 */
*/
  def printGoals(solver : Solver , gls : List[ProofGoal]) : String = {
    val res : ListBuffer[String] = ListBuffer()
    gls.foldLeft(1)((i , g) =>  {
      res += ("Goal " + i.toString + " :" + solver.presentObj(g.tp))
      i + 1
    })
    res.mkString("\n")
  }


  def printProofState(s : Solver ,   gls : List[ProofGoal]) : String ={
    if (gls.isEmpty) {return "done"}
    val goal = gls.head
    val goalName = s.checkingUnit.component
    val res : String = ">>>>>>>>>>>> PROVING: " + (if (goalName.isEmpty) {"Unnamed Goal"} else goalName.get.toString) + " <<<<<<<<<<<<<\n\n" +
      "HYPOTHESIS---------------HYPOTHESIS---------------HYPOTHESIS\n\n" +
      prettyprint.prettyPrintHyps(s , goal.stack) +
      "\n\n\nGOAL---------------GOAL---------------GOAL\n\n" + s.presentObj(goal.tp) + "\n\n\n" +
      printGoals(s , gls.tail)
    "<html>" + res.replaceAll("<","&lt;").replaceAll(">", "&gt;").replaceAll("\n", "<br/>") + "</html>"
  }


  def updateCheckingUnit(cu : CheckingUnit , p : ParseResult ): CheckingUnit = cu match {
    case CheckingUnit(component: Option[CPath], context: Context, unknowns: Context, judgement: WFJudgement) => {
      CheckingUnit(component , context , unknowns ++ p.unknown ,  judgement)
    }
  }

  def genFresh( ln : LocalName , ctx : Context) : LocalName = {
    var freeln = ln
    var cnt = 0
    while(ctx.index(freeln).isDefined){
      freeln = LocalName(ln.toString)/ LocalName(cnt.toString)
      cnt += 1
    }
    freeln
  }


  def genFreshHole( ln : LocalName , ctx : Context , prover : ImperativeProver) : LocalName = {

    var cnt = prover.goalCounter
    var freeln = LocalName(ln.toString)/ LocalName(cnt.toString)
    while(ctx.index(freeln).isDefined){
      freeln = LocalName(ln.toString)/ LocalName(cnt.toString)
      cnt += 1
    }
    prover.goalCounter = cnt
    freeln
  }

  def genHoleName(ctx : Context, prover : ImperativeProver) : LocalName = {
    val tmp = genFreshHole(LocalName("!!") , ctx , prover)
    tmp
  }

  def removeDed(t : Term) : Term = t match {
    case Proofs.ded(trm) => trm
    case _ => t
  }

}
