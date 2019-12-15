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

    unsigned int binaryLog(mpz_class v) {
      if (v.fits_ulong_p()) {
        unsigned long v_ul = v.get_ui();
        unsigned int res = 0;
        while (v_ul >>= 1) { ++res; }
        return res;
      }
      // TODO: implement this
      throw std::logic_error("Not implemented yet!");
    }

    mpz_class power(unsigned long base, unsigned long exp) {
      mpz_class res;
      mpz_ui_pow_ui(res.get_mpz_t(), base, exp);
      return res;
    }

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
            Expr bvvar = entry.first;
            Expr bv_one = bv::bvnum(1, 1, bvvar->getFactory());
            Expr boolVarToBVExpr = mk<EQ>(bvvar, bv_one);
            backSubMap.insert(std::make_pair(entry.second, boolVarToBVExpr));
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
//          std::cout << e << std::endl;
          Expr lhs = e->left();
          Expr rhs = e->right();
          bool varLhs = has(lhs);
          bool varRhs = has(rhs);
          if (varLhs || varRhs) {
            if (varLhs && varRhs) {
              Expr res = mk<EQ>(subMap.at(lhs), subMap.at(rhs));
              return VisitAction::changeTo(res);
            }
            Expr var = varLhs ? lhs : rhs;
            Expr other = varLhs ? rhs : lhs;
            if (isOpX<BOOL2BV>(other)) {
              Expr res = mk<EQ>(subMap.at(var), other->first());
              return VisitAction::changeDoKids(res);
            }
          }
        }
        if (isOpX<BOOL2BV>(e)) {
          ExprFactory& efac = e->getFactory();
          Expr bvone = bv::bvnum(mkTerm (mpz_class (1), efac), bv::bvsort(1, efac));
          Expr bvzero = bv::bvnum(mkTerm (mpz_class (0), efac), bv::bvsort(1, efac));
          Expr res = mk<ITE>(e->first(), bvone, bvzero);
          return VisitAction::changeDoKids(res);
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
      using inv_t = ExprMap;
      using subs_t = ExprMap;

      struct InvariantTranslator {
        InvariantTranslator(subs_t variableMap, subs_t declsMap) :
          variableMap{std::move(variableMap)},
          declsMap{std::move(declsMap)}
        {}

        inv_t translateInvariant(inv_t const& inv);
      private:
        std::map<Expr, Expr> variableMap;
        std::map<Expr, Expr> declsMap;

        Expr translateRecursively(Expr exp);

        static Expr translateOperation(Expr original, ExprVector n_args);

        int computeExpressionBitWidth(Expr e);
      };
      struct TranslationResult {
        Expr translated;
        BV2LIAPass::subs_t abstractions;
      };

      // Actual methods of BV2LIAPass

      void operator()(const CHCs & system);

      CHCs* getTransformed() { return transformed.get(); }

      InvariantTranslator getInvariantTranslator() const;

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
      void addRangeConstraints(const ufo::HornRuleExt &in, ufo::HornRuleExt &out);

      Expr translateVar(Expr var);
      TranslationResult translateGeneralExpression(Expr body);

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
        addRangeConstraints(clause, translated);
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
                           bind::intConst(bind::fname(bind::fname(var)))
                           : var;
        variableMap[var] = translatedVar;
        return translatedVar;
    }

    void BV2LIAPass::translateBody(const ufo::HornRuleExt &in, ufo::HornRuleExt &out) {
      auto result = translateGeneralExpression(in.body);
      out.body = result.translated;
      for (auto const & keyVal : result.abstractions) {
        out.locVars.push_back(keyVal.second);
      }
    }

    BV2LIAPass::TranslationResult BV2LIAPass::translateGeneralExpression(expr::Expr body) {
      RW<bv::BitWidthComputer> computer (new bv::BitWidthComputer());
      dagVisit(computer, body);
      auto bitwidthMap = computer._r->getBitWidths();
      // Using the Rewriter approach - rewrites expression from leaves to root
      bv::BV2LIATranslator translator(variableMap, declsMap, bitwidthMap);
      bv::BV2LIAVisitor visitor;
      visitor.setTranslator(&translator);
      Expr res = dagVisit(visitor, body);
      visitor.setTranslator(nullptr);
      return {res, translator.getAbstractionsMap()};
    }

    void BV2LIAPass::translateHead(const ufo::HornRuleExt &in, ufo::HornRuleExt &out) {
      if (in.isQuery) {
        // Fail declaration is treated differently, so manual handling of special case
        out.head = in.head;
        return;
      }
//      Expr head = in.head;
//      outs () << *head << "\n";
//      assert(bind::isFapp(head));
      Expr decl = in.head; //bind::fname(head);
      assert(declsMap.find(decl) != declsMap.end());
      Expr n_decl = declsMap.at(decl);
//      ExprVector n_args;
//      for (int i = 0; i < bind::domainSz(decl); ++i) {
//        Expr arg = head->arg(i + 1);
//        assert(variableMap.find(arg) != variableMap.end());
//        n_args.push_back(variableMap.at(arg));
//      }
//      Expr n_head = bind::fapp(n_decl, n_args);
      out.head = n_decl;
    }

    void BV2LIAPass::addRangeConstraints(const ufo::HornRuleExt &in, ufo::HornRuleExt &out) {
      if (in.isQuery) { return; } // No need for adding constraints to the query, if they are added to each transitions
      ExprVector constraints;
      auto& efac = in.body->getFactory();
      Expr zero = mkTerm (mpz_class (0), efac);
      auto varVecs = in.srcVars;
      for (auto const & varVec : varVecs) {
        for (Expr var : varVec) {
          assert(bind::isFapp(var));
          Expr varDecl = var->first();
          assert(bind::isFdecl(varDecl));
          Expr varType = bind::type(varDecl);
          if (!isBVSort(varType)) { continue; }
          int width = bv::width(varType);
          auto it = variableMap.find(var);
          assert(it != variableMap.end());
          Expr intVar = it->second;
          Expr lowerBound = mk<LEQ>(zero, intVar);
          mpz_class ubVal = power(2, width) - 1;
          Expr ubValExpr = mkTerm(ubVal, efac);
          Expr upperBound = mk<LEQ>(intVar, ubValExpr);
          constraints.push_back(lowerBound);
          constraints.push_back(upperBound);
        }
      }
      constraints.push_back(out.body);
      out.body = conjoin(constraints, efac);
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

    BV2LIAPass::InvariantTranslator BV2LIAPass::getInvariantTranslator() const {
      subs_t invertedDeclsMap;
      for (auto const& entry : this->declsMap) {
        invertedDeclsMap.insert(std::make_pair(entry.second, entry.first));
      }
      subs_t invertedVariableMap;
      for (auto const& entry : this->variableMap) {
        invertedVariableMap.insert(std::make_pair(entry.second, entry.first));
      }
      return BV2LIAPass::InvariantTranslator(std::move(invertedVariableMap), std::move(invertedDeclsMap));
    }

    BV2LIAPass::inv_t BV2LIAPass::InvariantTranslator::translateInvariant(const ufo::passes::BV2LIAPass::inv_t &inv) {
      BV2LIAPass::inv_t res;
      for (auto const& entry : inv) {
        Expr predicate = entry.first;
        Expr translatedPredicate;
        if (bind::isFdecl(predicate))
        {
          auto it = declsMap.find(predicate);
          assert(it != declsMap.end());
          translatedPredicate = it->second;
        }
        else
        {
          for (auto & a : declsMap)
          {
            if (a.first->left() == predicate)
            {
              translatedPredicate = a.second;
              break;
            }
          }
        }
        assert(translatedPredicate != NULL);
        Expr interpretation = entry.second;
        Expr translatedInterpretation = translateRecursively(interpretation);
        res.insert(std::make_pair(translatedPredicate, translatedInterpretation));
      }
      return res;
    }

    Expr BV2LIAPass::InvariantTranslator::translateRecursively(expr::Expr exp) {
      if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<IFF>(exp)) {
        ExprVector n_args;
        for (auto it = exp->args_begin(); it != exp->args_end(); ++it) {
          n_args.push_back(translateRecursively(*it));
        }
        return isOpX<AND>(exp) ? conjoin(n_args, exp->getFactory()) : disjoin(n_args, exp->getFactory());
      }
      if (isOpX<NEG>(exp)) {
        return mkNeg(translateRecursively(exp->first()));
      }
      if (isOp<ComparissonOp>(exp) || isOp<NumericOp>(exp)) {
        auto isConstant = bind::IsHardIntConst{};
        bool hasConstant = std::any_of(exp->args_begin(), exp->args_end(), isConstant);
        int opBitWidth = hasConstant ? computeExpressionBitWidth(exp) : 1; // 0 means unknown
        // If it does not contain constant, we don't care about the bitwidth
        assert(opBitWidth != 0);
        ExprVector n_args;
        for (auto it = exp->args_begin(); it != exp->args_end(); ++it) {
          Expr arg = *it;
          if (isConstant(arg)) {
            Expr n_const = bv::bvnum(arg, bv::bvsort(opBitWidth, exp->getFactory()));
            n_args.push_back(n_const);
          }
          else {
            n_args.push_back(translateRecursively(arg));
          }
        }
        // MB: TODO: Make this work, the problem is that it breaks bitwidth consistency, since expressions
        //      x/64 and extract(7,6,x) has different bitwidths for x of 8 bits
//        if (hasConstant && isOpX<IDIV>(exp) && n_args.size() == 2 && isConstant(exp->arg(1))) {
//          // if it is a power of two, we can model it as BV extract
//          mpz_class constant = getTerm<mpz_class>(exp->arg(1));
//          unsigned int exponent = binaryLog(constant);
//          if (power(2, exponent) == constant) {
//            return bv::extract(opBitWidth - 1, exponent, n_args[0]);
//          }
//        }

        Expr res = translateOperation(exp, n_args);
        return res;
      }
      if (bind::isBoolConst(exp)) {
         return exp;
      }
      if (isOpX<ITE>(exp)) {
        Expr then_o = exp->arg(1);
        Expr else_o = exp->arg(2);
        Expr cond_n = translateRecursively(exp->arg(0));
        auto isConstant = bind::IsHardIntConst{};
        bool hasConstant = std::any_of(exp->args_begin() + 1, exp->args_end(), isConstant);
        unsigned int opBitWidth = hasConstant ? computeExpressionBitWidth(exp) : 1; // 0 means unknown
        Expr then_n = isConstant(then_o) ? bv::bvnum(then_o, bv::bvsort(opBitWidth, exp->getFactory()))
            : translateRecursively(then_o);
        Expr else_n = isConstant(else_o) ? bv::bvnum(else_o, bv::bvsort(opBitWidth, exp->getFactory()))
                                         : translateRecursively(else_o);
        return mk<ITE>(cond_n, then_n, else_n);
      }
//      if (bind::isIntConst(exp)) {
        auto it = this->variableMap.find(exp);
        if (it != variableMap.end()) {
          return it->second;
        }
//      }

      std::cerr << "Unhandled case when translating LIA invariant to BV: " << *exp << std::endl;
      assert(false);
      throw std::logic_error("Unhandled case when translating LIA invariant to BV");
    }

    int BV2LIAPass::InvariantTranslator::computeExpressionBitWidth(Expr exp) {
      // MB: Apparently, the Integer variables are represented using BIND of String terminal and Simpe Type INT
      // This may originated already in our translation and needs to be checked!

      auto it = variableMap.find(exp);
      if (it != variableMap.end()) {
        Expr bvVar = it->second;
        assert(bind::isFapp(bvVar));
        Expr sort = bind::rangeTy(bvVar->first());
        return bv::width(sort);
      }
      if (bind::IsHardIntConst{}(exp)) {
        return 0; // = UNKNOWN
      }
      if (isOp<ComparissonOp>(exp) || isOp<NumericOp>(exp)) {
        auto it = exp->args_begin();
        auto end = exp->args_end();
        int res = 0;
        while (it != end) {
          res = computeExpressionBitWidth(*it);
          if (res != 0) { return res; }
          else ++it;
        }
        return 0; // UNKNOWN
      }
      if (isOpX<ITE>(exp)) {
        int res = 0;
        Expr then_exp = exp->arg(1);
        res = computeExpressionBitWidth(then_exp);
        if (res != 0) { return res; }
        Expr else_exp = exp->arg(2);
        res = computeExpressionBitWidth(else_exp);
        return res;
      }

      std::cerr << "Case not covered when computing bitwidth of an operation " << *exp << std::endl;
      assert(false);
      throw std::logic_error("Case not covered when bitwidth of an operation for translation from LIA to BV");
    }

    Expr BV2LIAPass::InvariantTranslator::translateOperation(Expr e, ExprVector n_args) {
      if (n_args.size() > 2) {
        ExprVector nn_args(n_args.begin() + 1, n_args.end());
        Expr subExpression = translateOperation(e, nn_args);
        n_args.erase(n_args.begin() + 1, n_args.end());
        n_args.push_back(subExpression);
      }
      if (isOpX<EQ>(e)) { return mknary<EQ>(n_args); }

      if (isOpX<NEQ>(e)) { return mknary<NEQ>(n_args); }

      if (isOpX<LEQ>(e)) { return mknary<BULE>(n_args); }

      if (isOpX<GEQ>(e)) { return mknary<BUGE>(n_args); }

      if (isOpX<LT>(e)) { return mknary<BULT>(n_args); }

      if (isOpX<GT>(e)) { return mknary<BUGT>(n_args); }

      if (isOpX<PLUS>(e)) { return mknary<BADD>(n_args); }

      if (isOpX<MINUS>(e)) { return mknary<BSUB>(n_args); }

      if (isOpX<MULT>(e)) { return mknary<BMUL>(n_args); }

      if (isOpX<IDIV>(e)) { return mknary<BUDIV>(n_args); }

      std::cerr << "Case not covered when translating operation from LIA to BV " << *e << std::endl;
      assert(false);
      throw std::logic_error("Case not covered when translating operation from LIA to BV");
    }

  }
}
#endif //SEAHORN_SIMPLIFICATIONPASSES_HPP
