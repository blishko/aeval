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
    const unsigned timeout_seconds = 1;
    const unsigned timeout_milisecs = timeout_seconds * 1000; // in miliseconds
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
//    ruleManager.print();
    CHCs original(ruleManager);
    ruleManager.simplifyCHCSystemSyntactically();
//    outs() << "After simplification:\n";
//    ruleManager.print();
//    outs () << "After slicing:\n";
    ruleManager.slice();
//    ruleManager.print();
    passes::BV1ToBool cleanup_pass;
    cleanup_pass(ruleManager);
//    outs() << "After cleanup:\n";
    CHCs* current = cleanup_pass.getCHCs();
//    current->print();
    passes::ITESimplificationPass itepass;
    itepass(*current);
//    current->print();
//    auto sol = current->solve(1);
//    if (!sol.empty()) {
//      std::cout << "Solution for simplified system found!" << std::endl;
//      for (auto& s : sol) {
//        std::cout << *s.first << " : " << *s.second << std::endl;
//      }
      // translate solution to the original system
//      sol = cleanup_pass.getInvariantTranslation().getOriginalSolution(sol);
//      std::map<Expr, ExprSet> candidates;
//      for (auto& s : sol) {
//        std::cout << *s.first << " : " << *s.second << std::endl;
//        candidates.insert(std::make_pair(bind::fname(s.first), ExprSet{s.second}));
//      }
//      NonlinCHCsolver nonlin (original);
//      nonlin.candidates = candidates;
//      vector<HornRuleExt*> worklist;
//      for (auto & hr : current->chcs) worklist.push_back(&hr);
//      nonlin.multiHoudini(worklist);
//      if(nonlin.checkAllOver(true)) {
//        std::cout << "Solved!\n";
//        exit(2);
//      }
//      else {
//        std::cout << "Somepart of invariant does not work\n";
//      }
//    }
    if (current->hasBV) {
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
        NonlinCHCsolver liaSyst(*current);
        if (liaSyst.guessAndSolve())
        {
          liaSyst.getSolution(solution);
        }
        else
        {
          // TODO: counterexample (using liaSyst.solveIncrementally)
          exit(0);
        }
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
          std::cout << "Somepart of invariant does not work\n";
        }
      }
    }
  };
}

#endif
