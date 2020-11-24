package latin2.proving

import java.awt.event.{ActionEvent, ActionListener, WindowEvent, WindowListener}

import info.kwarc.mmt.api.ErrorThrower
import info.kwarc.mmt.api.checking.{CheckingUnit, History, InferenceAndTypingRule, Solver, TypingRule}
import info.kwarc.mmt.api.documents.InterpretationInstructionContext
import info.kwarc.mmt.api.objects.{Context, Stack, Term}
import info.kwarc.mmt.api.parser.{NotationBasedParser, ParseResult, ParsingUnit, SourceRef}
import info.kwarc.mmt.lf.OfType
import lf.{PropositionsITP, Tactics}
import javax.swing._

import scala.collection.mutable.ListBuffer

object InteractiveProof extends InferenceAndTypingRule(Tactics.iproof.path ,OfType.path) {
  def apply(solver: Solver, tm: Term, tpO: Option[Term], covered : Boolean)(implicit stack: Stack, history: History): (Option[Term], Option[Boolean]) = {
    val Tactics.iproof(stps) = tm
    val tp = tpO.get //.getOrElse(return (None, None)) // for now we only use this as a checking rule, but inference is also possible
    var goal = ProofGoal(stack, tp, history + "starting prover")
    val rules = solver.rules.getOrdered(classOf[ProofStepRule])
    val prover = new InteractiveProver(solver, rules, goal)
    //   Solver.breakAfter(350)
    prover.executeProof(stps)
    if (prover.isSolved)
    {
      solver.report("proofstate" , "proof succeeded: " + solver.checkingUnit.component.toString ) ; (tpO,Some(true))
    } else
    {
      solver.report("proofstate" , "proof failed: " +  solver.checkingUnit.component.toString)  ; (tpO,None)
    }
  }
}



class InteractiveProver(var slvr : Solver, override val rules: List[ProofStepRule], initGoal: ProofGoal)  extends ImperativeProver(slvr , rules, initGoal)  {



  var history  : List[(Term , List[ProofGoal])] = Nil



  def executeProof(stps : List[Term]): Unit = {
    val lock = new Object
    SwingUtilities.invokeAndWait(new GuiProof)
    lock.synchronized{lock.wait()}
    class GuiProof extends Runnable {


      override def run(): Unit = {

        var steps = stps
        val jf: JFrame = new JFrame("Interactive Proof")
        jf.setSize(500, 500)
        jf.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)
        val splt0 = new JSplitPane(SwingConstants.HORIZONTAL)
        val splt1 = new JSplitPane(SwingConstants.VERTICAL)
        val splt2 = new JSplitPane(SwingConstants.HORIZONTAL)
        val proofStatePanel = new JPanel
        val stepHistoryPanel = new JPanel
        val inputPanel = new JPanel
        val completeProofPanel = new JPanel()
        val completeProofLabel = new JLabel(stps.map(x => solver.presentObj(x)).mkString("; "))
        completeProofPanel.add(completeProofLabel)
        splt0.setBottomComponent(splt2)
        splt0.setTopComponent(splt1)
        splt1.setLeftComponent(proofStatePanel)
        splt1.setRightComponent(stepHistoryPanel)
        splt2.setTopComponent(completeProofPanel)
        splt2.setBottomComponent(inputPanel)
        val proofStateLabel = new JLabel(helperFunctions.printProofState(solver, List(initGoal)))
        val stepHistoryLabel = new JLabel()
        proofStatePanel.add(proofStateLabel)
        stepHistoryPanel.add(stepHistoryLabel)
        val undoButton = new JButton("Undo Step")
        val forwardButton = new JButton("Step Forward")
        inputPanel.add(forwardButton)
        inputPanel.add(undoButton)
        forwardButton.addActionListener(new NextStep)
        undoButton.addActionListener(new UndoStep)
        jf.add(splt0)
        jf.setVisible(true)
        jf.addWindowListener(new WakeUp)


        class WakeUp() extends WindowListener {
          override def windowOpened(windowEvent: WindowEvent): Unit = ()

          override def windowClosing(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowClosed(windowEvent: _root_.java.awt.event.WindowEvent): Unit = {
            lock.synchronized{lock.notifyAll()}
          }

          override def windowIconified(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowDeiconified(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowActivated(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()

          override def windowDeactivated(windowEvent: _root_.java.awt.event.WindowEvent): Unit = ()
        }


        class NextStep() extends ActionListener {
          override def actionPerformed(ae: ActionEvent): Unit = {
            if (steps.isEmpty) {
              return
            }
            val step = steps.head
            steps = steps.tail
            makeStep(step)
            history = ((step, getGoals)) :: history
            val hsteps = history.map(x => solver.presentObj(x._1)).mkString(";")
            stepHistoryLabel.setText(hsteps)
            proofStateLabel.setText(helperFunctions.printProofState(solver, history.head._2))
          }
        }


        class UndoStep() extends ActionListener {
          override def actionPerformed(ae: ActionEvent): Unit = {
            if (history.isEmpty) return
            val (s, g) = history.head
            history =  if (history.isEmpty) Nil else history.tail
            val hsteps = history.map(x => solver.presentObj(x._1)).mkString(";")
            stepHistoryLabel.setText(hsteps)
            steps = s :: steps
            goals =  if (history.isEmpty) List(initGoal) else history.head._2
            proofStateLabel.setText(if (history.isEmpty) helperFunctions.printProofState(solver , List(initGoal)) else helperFunctions.printProofState(solver, history.head._2))
          }
        }
      }
    }
  }
}



/*


class InteractiveProver(var slvr : Solver, override val rules: List[ProofStepRule], initGoal: ProofGoal)  extends ImperativeProver(slvr , rules, initGoal)  {



  val history  : ListBuffer[(Option[Term] , List[ProofGoal])] = ListBuffer((None, List(initGoal)))


  val nbp : NotationBasedParser = solver.controller.extman.get(classOf[NotationBasedParser]).head
//  val context : Context =
//  val string = "type" // test
  //val pu = ParsingUnit(SourceRef.anonymous("fromGUI"),context,string,InterpretationInstructionContext(solver.controller.getNamespaceMap))
//  nbp(pu)(ErrorThrower)

  // var currentState : ProofHistoryStep = ProofHistoryStep(List(initGoal))


  def executeProof(): Unit = {
    solver.report("itp" , "start exe")
    val jf : JFrame = new JFrame("Interactive Proof")
    jf.setSize(500 , 500)
    jf.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)
    val splt0 = new JSplitPane(SwingConstants.HORIZONTAL)
 //   splt0.setDividerLocation(0.7)
    val splt1 = new JSplitPane(SwingConstants.VERTICAL)
    val proofStatePanel = new JPanel
    val stepHistoryPanel = new JPanel
    val inputPanel = new JPanel
    splt0.setBottomComponent(inputPanel)
    splt0.setTopComponent(splt1)
    splt1.setLeftComponent(proofStatePanel)
    splt1.setRightComponent(stepHistoryPanel)
    val proofStateLabel = new JLabel(helperFunctions.printProofState(solver  , history.head._2))
    val stepHistoryLabel = new JLabel()
    proofStatePanel.add(proofStateLabel)
    stepHistoryPanel.add(stepHistoryLabel)
    val undoButton = new JButton("Undo Step")
    val inputText = new JTextField("input your tactics here" , 40)
    inputPanel.add(inputText)
    inputPanel.add(undoButton)
    inputText.addActionListener(new NextStep)
    undoButton.addActionListener(new UndoStep)
    jf.add(splt0)
    jf.setVisible(true)
    solver.report("itp" , "in execute proof ")

    class NextStep() extends ActionListener {
      override def actionPerformed(ae: ActionEvent): Unit = {
        val input = inputText.getText()
        inputText.setText("")
        val ctx = solver.checkingUnit.context
        val pu = ParsingUnit(SourceRef.anonymous("fromGUI"),ctx,input,InterpretationInstructionContext(solver.controller.getNamespaceMap))
        var res : ParseResult  = nbp(pu)(ErrorThrower)
        val step = res.term
        solver = new Solver(solver.controller , helperFunctions.updateCheckingUnit(solver.checkingUnit , res) , solver.rules)
        makeStep(step)
        genCurrStateAndHistoryStep(step)
        val hsteps = history.map(x => x._1 match {case None => "" ; case (Some(s)) => s.toString }).mkString(";")
        stepHistoryLabel.setText(hsteps)
        proofStateLabel.setText(helperFunctions.printGoals(solver , history.head._2))
        solver.report("itp" , "testtest")
      }
    }


    def genCurrStateAndHistoryStep(s : Term): Unit = {
      history.prepend((Some(s) , getGoals))

    }


    class UndoStep() extends ActionListener{
      override def actionPerformed(ae: ActionEvent): Unit = {

      }
    }

  }









}

 */