#ifndef THEOREFCHCSOLVER__HPP__
#define THEOREFCHCSOLVER__HPP__

#include "NonlinCHCsolver.hpp"
#include "simpl/SimplificationPasses.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  inline void solve(string smt, bool spacer)
  {
    const unsigned timeout_seconds = 5;
    const unsigned timeout_milisecs = timeout_seconds * 1000; // in miliseconds
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
//    outs() << "After parsing:\n";
//    ruleManager.print();
    CHCs original(ruleManager);
    ruleManager.simplifyCHCSystemSyntactically();
//    outs() << "After simplification:\n";
//    ruleManager.print();
    ruleManager.slice();
//    outs () << "After slicing:\n";
//    ruleManager.print();
    passes::BV1ToBool cleanup_pass;
    cleanup_pass(ruleManager);
//    outs() << "After cleanup:\n";
    CHCs* current = cleanup_pass.getCHCs();
//    current->print();
    passes::ITESimplificationPass itepass;
    itepass(*current);
    if (current->hasBV) {
      CHCs* lastBVSystem = current;
      passes::BV2LIAPass bv2lia;
      bv2lia(*current);
      current = bv2lia.getTransformed();
//      outs() << "LIA translation:\n";
//      current->print();
      ExprMap solution;
      if (spacer)
      {
        solution = current->solve();
      }
      else
      {
        // MB: First try to find some useful invariants with FreqHorn
        NonlinCHCsolver liaSyst(*current);
//        std::cout << "Running guessAndSolve\n" << std::endl;
        const bool invariantFound = liaSyst.guessAndSolve(false); // MB: not necessarily safe invariant!
//        std::cout << "guessAndSolve finished" << std::endl;
        if (invariantFound)
        {
          liaSyst.getSolution(solution, false);
          if (liaSyst.checkQuery(solution)) {
            // It is a safe invariant for LIA translation, no need to do additional work on LIA representation
          }
          else {
            // strengthen and run spacer?
            current->strengthenWithInvariants(solution);
            auto spacerSolution = current->solve(timeout_milisecs);
            if (!spacerSolution.empty()) {
              solution = spacerSolution; // MB: or combine them together?
            }
          }
          // solution contains some invariants that can be used to strengthen the transition relation
          // Translate to BV and check if they are invariants there
          auto invariantTranslator = bv2lia.getInvariantTranslator();
          auto translated = invariantTranslator.translateInvariant(solution);
//          std::cout << "Translated solution:\n";
//            for (auto const& entry : translated) {
//            std::cout << *entry.first << " - " << *entry.second << '\n';
//            }
          {
            map<Expr, ExprSet> candidates;
            for (auto& s : translated) {
              ExprSet tmp;
              getConj(s.second, tmp);
              candidates.insert(std::make_pair(bind::fname(s.first), tmp));
            }
            NonlinCHCsolver bvsolver (*lastBVSystem);
            bool invariantsFound = bvsolver.filterAndSolve(candidates, false); // We do not care if the invariant is safe
            if (invariantFound) {
              // BV invariant, let's add it to the transition relations, see if it simplifies anything
              ExprMap bvInvariants;
              bvsolver.getSolution(bvInvariants);
              // TEST if it is not safe invariant
              bvsolver.setCandidates(bvInvariants);
              if (bvsolver.checkAllOver(true)) {
                std::cout << "Safe Invariant found!" << std::endl;
                exit(0);
              }
              // Not Safe invariant, so strengthen and continue
              lastBVSystem->strengthenWithInvariants(bvInvariants);
//              lastBVSystem->print();
              auto bvsolution = lastBVSystem->solve(timeout_milisecs);
              if(!bvsolution.empty()) {
                std::cout << "BV solution found after strengthening with invariants from LIA\n";
              }
              else{
                std::cout << "UNKNOW" << std::endl;
              }
            }
            else {
              // No new invariant learnt
              std::cout << "UNKNOW" << std::endl;
            }
          }
        }
        else
        {
          std::cout << "Guess and solve failed!" << std::endl;
          // TODO: counterexample (using liaSyst.solveIncrementally)
          exit(0);
        }
        exit(0);
      }
      if (!solution.empty()) {
//        std::cout << "Solution in LIA found!\n";
//        for (auto const& entry : solution) {
//          std::cout << *entry.first << " - " << *entry.second << '\n';
//        }
        auto invariantTranslator = bv2lia.getInvariantTranslator();
        auto translated = invariantTranslator.translateInvariant(solution);
//        std::cout << "Translated solution:\n";
//        for (auto const& entry : translated) {
//          std::cout << *entry.first << " - " << *entry.second << '\n';
//        }
        auto originalSol = cleanup_pass.getInvariantTranslation().getOriginalSolution(translated);
        std::map<Expr, ExprSet> candidates;
        for (auto& s : originalSol) {
          ExprSet tmp;
          getConj(s.second, tmp);
          candidates.insert(std::make_pair(bind::fname(s.first), tmp));
//          std::cout << *bind::fname(s.first) << " - " << *s.second << std::endl;
        }
        NonlinCHCsolver nonlin (original);
        if(nonlin.filterAndSolve(candidates)) {
          std::cout << "Solved!\n";
        }
        else {
          std::cout << "Some part of invariant does not work\n";
        }
      }
      else {
        std::cout << "LIA Spacer found counterexample" << std::endl;
      }
    }
  };
}

#endif
