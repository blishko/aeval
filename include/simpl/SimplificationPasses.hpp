//
// Created by Martin Blicha on 05.11.19.
//

#ifndef SEAHORN_SIMPLIFICATIONPASSES_HPP
#define SEAHORN_SIMPLIFICATIONPASSES_HPP

#include "deep/HornNonlin.hpp"
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp"

namespace ufo {
  namespace passes {
    struct DeconstructVariables {

      std::unique_ptr<CHCs> res;

      void operator()(const CHCs &in);

    };


    struct BV1ToBool {
    private:
      // Variable mapping
      using subs_t = std::map<Expr, Expr>;
      subs_t substitutionMap;
      static Expr rewrite(Expr expr, const std::map<Expr, Expr>& subMap);
    public:
      struct InvariantTranslation {
      private:
        std::map<Expr, Expr> backSubMap;
      public:
        InvariantTranslation(const subs_t& originalMap) {
          for(const auto& entry : originalMap) {
            backSubMap.insert(std::make_pair(entry.second, entry.first));
          }
        }

        std::map<Expr, Expr> getOriginalSolution(const std::map<Expr, Expr>& translatedSolution) {
          subs_t res;
          for (auto const& entry : translatedSolution) {
            res.insert(std::make_pair(entry.first, replace(entry.second, backSubMap)));
          }
          return res;
        }
      };

      std::unique_ptr<CHCs> res;

      InvariantTranslation getInvariantTranslation() const {
        return InvariantTranslation(substitutionMap);
      }

      CHCs* getCHCs() const { return res.get(); }

      void operator()(const CHCs &in) {
        auto *copy = new CHCs(in);
        res = std::unique_ptr<CHCs>(copy);
        std::unordered_set<Expr> bv1vars;
        auto isBV1 = [](Expr exp) { return bv::is_bvconst(exp) && bv::width(exp->first()->right()) == 1; };
        for (auto const& chc : in.chcs) {
          // get BV1 variables
          std::copy_if(chc.dstVars.begin(), chc.dstVars.end(), std::inserter(bv1vars, bv1vars.end()),
              isBV1);
          for (auto const& srcVars : chc.srcVars) {
            std::copy_if(srcVars.begin(), srcVars.end(), std::inserter(bv1vars, bv1vars.end()),
                         isBV1);
          }
        }
//        for (Expr bv1var: bv1vars) {
//          std::cout << *bv1var << ' ';
//        }
//        std::cout << std::endl;
        // create a boolean version for the variables and remember the mapping
        this->substitutionMap.clear();
        for (Expr bv1var: bv1vars) {
          Expr sub = bind::boolConst(mkTerm<std::string>(lexical_cast<string>(bv1var), bv1var->getFactory()));
          this->substitutionMap[bv1var] = sub;
        }
        // replace the variables in all CHCs
        std::map<Expr, Expr> sort_replacement;
        auto& factory = res->m_efac;
        sort_replacement[bv::bvsort(1,factory)] = mk<BOOL_TY>(factory);
        const auto& subMap = this->substitutionMap;
        auto varReplace = [&subMap](Expr e) { return replace(e, subMap);};
        for (auto& chc : res->chcs) {
          chc.body = this->rewrite(chc.body, subMap);
          assert(isOpX<FDECL>(chc.head));
          chc.head = replace(chc.head, sort_replacement);
          std::transform(chc.dstVars.begin(), chc.dstVars.end(), chc.dstVars.begin(), varReplace);

          std::transform(chc.locVars.begin(), chc.locVars.end(), chc.locVars.begin(),
                         varReplace);
          for (auto& srcVars : chc.srcVars) {
            std::transform(srcVars.begin(), srcVars.end(), srcVars.begin(),
                          varReplace);
          }
        }
        ExprSet newdecls;
        for (auto& decl : res->decls) {
          newdecls.insert(replace(decl, sort_replacement));
        }
        res->decls = newdecls;
        for (auto& entry : res->invVars) {
          ExprVector& vars = entry.second;
          std::transform(vars.begin(), vars.end(), vars.begin(),
                         varReplace);
        }
      }
    };

    struct BV1ToBoolRewrite {
    private:
      const std::map<Expr,Expr>& subMap;
      bool has(Expr e) const { return subMap.find(e) != subMap.end(); }
    public:
      BV1ToBoolRewrite(const std::map<Expr,Expr>& subMap) : subMap{subMap} {}
      VisitAction operator()(Expr e) {
        if (isOpX<BV2BOOL>(e)) {
          if (has(e->first())) {
            return VisitAction::changeTo(subMap.at(e->first()));
          }
          // rewrite BV2BOOL(x) back to x == 1;
          Expr res = mk<EQ>(e->first(),
              bv::bvnum(mkTerm (mpz_class (1), e->getFactory()), bv::bvsort(1, e->getFactory())));
          return VisitAction::changeDoKids(res);
        }
        if (isOpX<EQ>(e)) {
          Expr lhs = e->left();
          Expr rhs = e->right();
          bool varLhs = has(lhs);
          bool varRhs = has(rhs);
          if (varLhs || varRhs) {
            Expr var = varLhs ? lhs : rhs;
            Expr other = varLhs ? rhs : lhs;
            if (isOpX<BOOL2BV>(other)) {
              Expr res = mk<EQ>(subMap.at(var), other->first());
              return VisitAction::changeDoKids(res);
            }
          }
        }
        // TODO: add cases as needed, or default to var_bv <=> ite(var_bool, 1, 0)
        return VisitAction::doKids();
      }
    };

    inline Expr BV1ToBool::rewrite(Expr expr, const std::map<Expr,Expr>& subMap) {
      BV1ToBoolRewrite visitor(subMap);
      return dagVisit(visitor, expr);
    }
  }
}
#endif //SEAHORN_SIMPLIFICATIONPASSES_HPP
