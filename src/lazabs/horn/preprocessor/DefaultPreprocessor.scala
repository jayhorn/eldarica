/**
 * Copyright (c) 2016 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.preprocessor

import ap.parser._
import ap.SimpleAPI
import IExpression._

import lazabs.horn.bottomup.HornClauses
import lazabs.horn.global._
import lazabs.horn.bottomup.Util.Dag

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Default preprocessing pipeline used in Eldarica.
 */
class DefaultPreprocessor extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "default"
  val printWidth = 55

  val preStages : List[HornPreprocessor] =
    List(ReachabilityChecker,
         BooleanClauseSplitter)

  val postStages : List[HornPreprocessor] =
    (if (lazabs.GlobalParameters.get.slicing)
      List(Slicer) else List()) ++
    List(new ClauseShortener) ++
    (if (lazabs.GlobalParameters.get.splitClauses)
      List(new ClauseSplitter) else List()) ++
    (if (lazabs.GlobalParameters.get.staticAccelerate)
      List(Accelerator) else List())

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    var curClauses = clauses
    var curHints = hints

    Console.err.println(
         "------------------------------- Preprocessing ----------------------------------")
    Console.err.println("Initially:" + (" " * (printWidth - 10)) +
                        curClauses.size + " clauses")

    val translators = new ArrayBuffer[BackTranslator]

    def applyStage(stage : HornPreprocessor) = {
      val startTime = System.currentTimeMillis

      val (newClauses, newHints, translator) =
        stage.process(curClauses, curHints)
      curClauses = newClauses
      curHints = newHints

      val time = "" + (System.currentTimeMillis - startTime) + "ms"
      val prefix = "After " + stage.name + " (" + time + "):"

      Console.err.println(prefix + (" " * (printWidth - prefix.size)) +
                          curClauses.size + " clauses")

      translators += translator
    }

    // First set of processors
    for (stage <- preStages)
      applyStage(stage)

    // Apply clause simplification and inlining repeatedly, if necessary
    applyStage(DefinitionInliner)
    applyStage(new ClauseInliner)

    var lastSize = -1
    var curSize = curClauses.size
    while (lastSize != curSize) {
      lastSize = curSize
      applyStage(DefinitionInliner)
      curSize = curClauses.size

      if (curSize != lastSize) {
        lastSize = curSize
        applyStage(new ClauseInliner)
        curSize = curClauses.size
      }
    }

    // Last set of processors
    for (stage <- postStages)
      applyStage(stage)

    Console.err.println

    (curClauses, curHints, new ComposedBackTranslator(translators.reverse))
  }

}

////////////////////////////////////////////////////////////////////////////////

object AbductionPreprocessor extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "abduction simplifier"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    var curClauses = clauses
    var curHints = hints

    val translators = new ArrayBuffer[BackTranslator]

    def applyStage(stage : HornPreprocessor) = {
      val (newClauses, newHints, translator) =
        stage.process(curClauses, curHints)
      curClauses = newClauses
      curHints = newHints

      translators += translator
    }

    // Apply clause simplification and inlining repeatedly, if necessary
    applyStage(ReachabilityChecker)
    applyStage(DefinitionInliner)
    applyStage(new ClauseInliner)
    applyStage(ConstraintSatChecker)

    var lastSize = -1
    while (lastSize != curClauses.size) {
      lastSize = curClauses.size
      applyStage(ReachabilityChecker)
      applyStage(DefinitionInliner)
      applyStage(new ClauseInliner)
      applyStage(ConstraintSatChecker)
    }

    (curClauses, curHints, new ComposedBackTranslator(translators.reverse))
  }

}

////////////////////////////////////////////////////////////////////////////////

// Remove all clauses with unsatisfiable constraint
object ConstraintSatChecker extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "constraint sat checker"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val newClauses = SimpleAPI.withProver { p =>
      import p._

      for (clause <- clauses;
           if !(clause.body contains clause.head);
           if (try { p.scope {
             addRelations(clause.predicates.toSeq)
             ?? (clause.toFormula)
             withTimeout(1000) {
               ??? != SimpleAPI.ProverStatus.Valid
             }
           } } catch {
             case SimpleAPI.TimeoutException => true
           }))
      yield clause
    }

    (newClauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)
  }

}