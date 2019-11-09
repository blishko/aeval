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
        const bool isBV2BOOL = isOpX<BV2BOOL>(e) || (isOpX<NEG>(e) && isOpX<BV2BOOL>(e->first()));
        if (isBV2BOOL) {
          const bool isNegated = isOpX<NEG>(e);
          const Expr argument = isNegated ? e->first()->first() : e->first();
          if (has(argument)) {
            Expr changed = isNegated ? mk<NEG>(subMap.at(argument)) : subMap.at(argument);
            return VisitAction::changeTo(changed);
          }
          // rewrite BV2BOOL(x) back to x == 1;
          Expr res = mk<EQ>(argument,
              bv::bvnum(mkTerm (mpz_class (isNegated ? 0 : 1), e->getFactory()), bv::bvsort(1, e->getFactory())));
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

    struct ITESimplificationPass {
      void operator()(CHCs &in) {
        SMTUtils smtutils(in.m_efac);
        ITEVisitor v(smtutils);
        for (auto& chc : in.chcs) {
          chc.body = dagVisit(v, chc.body);
        }
      }

      struct ITEVisitor {
        SMTUtils& smtutils;

        ITEVisitor(SMTUtils& smtutils) : smtutils{smtutils} {}

        VisitAction operator()(Expr e) {
          if (isOpX<ITE>(e)) {
            ExprVector pos;
            ExprVector neg;
            Expr res = simplifyITE(e, pos, neg);
            return VisitAction::changeTo(res);
          }
          return VisitAction::doKids();
        }

        Expr simplifyITE(Expr ex, ExprVector& trueConditions, ExprVector& falseConditions)
        {
          if (bv::is_bvnum(ex) || bv::is_bvconst(ex)) { return ex; }
//          std::cout << *ex << std::endl;
          auto& fact = ex->getFactory();
          ExprVector substituteWhat;
          ExprVector substituteWith;
          for (Expr e : trueConditions) {
            substituteWhat.push_back(e);
            substituteWith.push_back(mk<TRUE>(ex->getFactory()));
          }
          for (Expr e : falseConditions) {
            substituteWhat.push_back(e);
            substituteWith.push_back(mk<FALSE>(ex->getFactory()));
          }
          ex = replaceAll(ex, substituteWhat, substituteWith);

          if (isOpX<ITE>(ex)){

            Expr cond = simplifyITE(ex->arg(0), trueConditions, falseConditions);
            Expr br1 = ex->arg(1);
            Expr br2 = ex->arg(2);

            Expr ret;
            Expr upLevelCond = conjoin(trueConditions, fact);
            if (!smtutils.isSat(cond, upLevelCond)) {
              falseConditions.push_back(cond);
              trueConditions.push_back(mkNeg(cond));
              Expr res = simplifyITE(br2, trueConditions, falseConditions);
              falseConditions.pop_back();
              trueConditions.pop_back();
              return res;
            }
            if (!smtutils.isSat(mk<NEG>(cond), upLevelCond)) {
              trueConditions.push_back(cond);
              falseConditions.push_back(mkNeg(cond));
              Expr res = simplifyITE(br1, trueConditions, falseConditions);
              trueConditions.pop_back();
              falseConditions.pop_back();
              return res;
            }
            trueConditions.push_back(cond);
            falseConditions.push_back(mkNeg(cond));
            Expr n_then = simplifyITE(br1, trueConditions, falseConditions);
            trueConditions.pop_back();
            falseConditions.pop_back();
            falseConditions.push_back(cond);
            trueConditions.push_back(mkNeg(cond));
            Expr n_else = simplifyITE(br2, trueConditions, falseConditions);
            falseConditions.pop_back();
            trueConditions.pop_back();
            return mk<ITE>(cond,n_then, n_else);
          }

          else {
            if (ex->arity() == 0) { return ex; }
            ExprVector kids;
            std::transform(ex->args_begin(), ex->args_end(), std::back_inserter(kids),
                [this, &trueConditions, &falseConditions](Expr e) {
              return this->simplifyITE(e, trueConditions, falseConditions);
            });
            Expr res = ex->getFactory().mkNary(ex->op(), kids);
            return res;
          }
        }
      };
    };

    struct BV2LIAPass {
      void operator()(const CHCs & system);

      CHCs* getTransformed() { return transformed.get(); }
    private:
      std::unique_ptr<CHCs> transformed;

      std::map<Expr, Expr> variableMap;
      std::map<Expr, Expr> declsMap;


      ExprSet translateDeclarations(const ExprSet& originals);
      std::vector<HornRuleExt> translateClauses(const std::vector<HornRuleExt>& originals);
      std::map<Expr, ExprVector> translateInvVars(const std::map<Expr, ExprVector>& originals);

      void translateVariables(const HornRuleExt & in, HornRuleExt & out);
      void translateBody(const HornRuleExt & in, HornRuleExt & out);
      void translateHead(const HornRuleExt & in, HornRuleExt & out);

      Expr translateVar(Expr var);
      Expr translateGeneralExpression(Expr body);

      static bool isBVVar(Expr e) { return isOpX<FAPP>(e) && isBVSort(e->first()->last()); }
      static bool isBVSort(Expr e) { return isOpX<BVSORT>(e); }
    };

    void BV2LIAPass::operator()(const CHCs & system) {
      transformed.reset( new CHCs {system.m_efac, system.m_z3});
      CHCs& liaSystem = *transformed;

      liaSystem.decls = translateDeclarations(system.decls);
      // FAIL is the same
      liaSystem.failDecl = system.failDecl;
      // translated each CHC
      liaSystem.chcs = translateClauses(system.chcs);
      // translate var info
      liaSystem.invVars = translateInvVars(system.invVars);
      // translate incms
      // TODO: test what is the key
      liaSystem.incms = system.incms;
    }

    ExprSet BV2LIAPass::translateDeclarations(const ExprSet & originals) {
      ExprSet ret;
      for (const auto& decl : originals) {
        assert(bind::isFdecl(decl));
        ExprVector types;
        for (int i = 1; i < decl->arity(); ++i) {
          Expr arg = decl->arg(i);
          Expr type = isOpX<BVSORT>(arg) ? sort::intTy(arg->getFactory()) : arg;
          types.push_back(type);
        }
        Expr name = bind::fname(decl);
        Expr translated = bind::fdecl(name, types);
        declsMap[decl] = translated;
        ret.insert(translated);
      }
      return ret;
    }

    std::vector<HornRuleExt> BV2LIAPass::translateClauses(const std::vector<HornRuleExt> & originals) {
      std::vector<HornRuleExt> ret;
      for (const auto& clause : originals) {
        ret.emplace_back();
        HornRuleExt& translated = ret.back();
        // set flags
        translated.isQuery = clause.isQuery;
        translated.isFact = clause.isFact;
        translated.isInductive = clause.isInductive;

        translateVariables(clause, translated);

        translateBody(clause, translated);

        translateHead(clause, translated);
        // copy the relations, these are just names
        assert(isOpX<STRING>(clause.dstRelation));
        translated.dstRelation = clause.dstRelation;
        translated.srcRelations = clause.srcRelations;
      }
      return ret;
    }

    void BV2LIAPass::translateVariables(const ufo::HornRuleExt &in, ufo::HornRuleExt &out) {
      // src variables
      for (const auto& srcVars : in.srcVars) {
        ExprVector translatedVars;
        for (const auto& var : srcVars) {
          Expr translatedVar = translateVar(var);
          translatedVars.push_back(translatedVar);
        }
        out.srcVars.push_back(translatedVars);
      }
      // dst variables
      for (const auto& dstVar : in.dstVars) {
        out.dstVars.push_back(translateVar(dstVar));
      }
      // local variables
      for (const auto& locVar : in.locVars) {
        out.locVars.push_back(translateVar(locVar));
      }
    }

    Expr BV2LIAPass::translateVar(expr::Expr var) {
      auto it = this->variableMap.find(var);
      if (it != variableMap.end()) { return it->second; }
      Expr translatedVar = this->isBVVar(var) ?
                           bind::intVar(bind::fname(bind::fname(var)))
                           : var;
        variableMap[var] = translatedVar;
        return translatedVar;
    }

    void BV2LIAPass::translateBody(const ufo::HornRuleExt &in, ufo::HornRuleExt &out) {
      out.body = translateGeneralExpression(in.body);
    }

    Expr BV2LIAPass::translateGeneralExpression(expr::Expr body) {
      // Using the Rewriter approach - rewrites expression from leaves to root
      RW<bv::BV2LIATranslator> rw (new bv::BV2LIATranslator(variableMap, declsMap));
      Expr res = dagVisit(rw, body);
      return res;
    }

    void BV2LIAPass::translateHead(const ufo::HornRuleExt &in, ufo::HornRuleExt &out) {
      if (in.isQuery) {
        // Fail declaration is treated differently, so manual handling of special case
        out.head = in.head;
        return;
      }
      Expr head = in.head;
      assert(bind::isFapp(head));
      Expr decl = bind::fname(head);
      assert(declsMap.find(decl) != declsMap.end());
      Expr n_decl = declsMap.at(decl);
      ExprVector n_args;
      for (int i = 0; i < bind::domainSz(decl); ++i) {
        Expr arg = head->arg(i + 1);
        assert(variableMap.find(arg) != variableMap.end());
        n_args.push_back(variableMap.at(arg));
      }
      Expr n_head = bind::fapp(n_decl, n_args);
      out.head = n_head;
    }

    std::map<Expr, ExprVector> BV2LIAPass::translateInvVars(const map<Expr, ExprVector> & originals) {
      std::map<Expr, ExprVector> res;
      for (const auto& entry : originals) {
        Expr predicate = entry.first;
        assert(isOpX<STRING>(predicate));
        const auto& vars = entry.second;
        ExprVector translatedVars;
        for (const auto& var : vars) {
          assert(variableMap.find(var) != variableMap.end());
          translatedVars.push_back(variableMap.at(var));
        }
        res.insert(std::make_pair(predicate, translatedVars));
      }
      return res;
    }
  }
}
#endif //SEAHORN_SIMPLIFICATIONPASSES_HPP
