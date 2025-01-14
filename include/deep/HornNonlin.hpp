#ifndef HORNNONLIN__HPP__
#define HORNNONLIN__HPP__

#include "ae/AeValSolver.hpp"
#include "ufo/ExprTranslations.h"

using namespace std;
using namespace boost;

namespace ufo
{
  // all adapted from Horn.hpp; experimental; to merge with Horn.hpp at some point
  inline bool rewriteHelperConsts(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    vector<ExprVector> srcVars;
    ExprVector dstVars; // These are FAPPs!
    ExprVector locVars;

    Expr body;
    Expr head;

    ExprVector srcRelations;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (vector<ExprVector>& _srcVars, vector<ExprVector>& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        ExprVector tmp;
        for (int j = 0; j < _srcVars[i].size(); j++)
        {
          tmp.push_back(invVarsSrc[i][j]);
          body = mk<AND>(body, mk<EQ>(_srcVars[i][j], tmp[j]));
        }
        srcVars.push_back(tmp);
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
      }
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    ExprSet decls;
    Expr failDecl;
    vector<HornRuleExt> chcs;
    map<Expr, ExprVector> invVars;
    map<Expr, vector<int>> incms;
    int qCHCNum;  // index of the query in chc
    int total_var_cnt = 0;
    bool hasBV = false;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3)  {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->arg(0)))
            if (e->arg(0)->arity() >= 2)
              return true;
      return false;
    }

    void preprocess (Expr term, ExprVector& locVars, vector<ExprVector>& srcVars, ExprVector &srcRelations, ExprSet& lin)
    {
      if (isOpX<AND>(term))
      {
        for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it)
        {
          preprocess(*it, locVars, srcVars, srcRelations, lin);
        }
      }
      else
      {
        if (bind::isBoolConst(term))
        {
          lin.insert(term);
        }
        if (isOpX<FAPP>(term) && find(locVars.begin(), locVars.end(), term) == locVars.end())
        {
          if (term->arity() > 0)
          {
            if (isOpX<FDECL>(term->arg(0)))
            {
              Expr rel = term->arg(0);
              if (rel->arity() >= 2)
              {
                addDecl(rel);
                srcRelations.push_back(rel->arg(0));
                ExprVector tmp;
                for (auto it = term->args_begin()+1, end = term->args_end(); it != end; ++it)
                  tmp.push_back(*it);
                srcVars.push_back(tmp);
              }
            }
          }
        }
        else
        {
          lin.insert(term);
        }
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a->arg(0)].size() == 0)
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          total_var_cnt++;
          Expr var;
          if (isOpX<INT_TY> (a->arg(i)))
            var = bind::intConst(new_name);
          else if (isOpX<REAL_TY> (a->arg(i)))
            var = bind::realConst(new_name);
          else if (isOpX<BOOL_TY> (a->arg(i)))
            var = bind::boolConst(new_name);
          else if (isOpX<ARRAY_TY> (a->arg(i))) // GF: currently support only arrays over Ints
          {
            var = bind::mkConst(new_name, mk<ARRAY_TY>
                  (mk<INT_TY> (m_efac), mk<INT_TY> (m_efac)));
          }
          else if (isOpX<BVSORT> (a->arg(i))) {
            var = bv::bvConst(new_name, bv::width(a->arg(i)));
            hasBV = true;
          }
          invVars[a->arg(0)].push_back(var);
        }
      }
    }

    void parse(string smt)
    {
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      for (auto &r: fp.m_rules)
      {
        bool toReplace = false;
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        Expr rule = r;
        while (isOpX<FORALL>(r))
        {
          toReplace = true;
          for (int i = 0; i < r->arity() - 1; i++)
          {
            hr.locVars.push_back(bind::fapp(r->arg(i)));
          }
          r = r->last();
        }

        if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
        {
          toReplace = true;
          for (int i = 0; i < r->first()->arity() - 1; i++)
            hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

          rule = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
          r = rule;
        }

        if (toReplace)
        {
          if (isOpX<NEG>(r))
          {
            rule = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
          }
          else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
          {
            rule = mk<IMPL>(r->left()->left(), r->right());
          }
          else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
          {
            rule = mk<IMPL>(r->right()->left(), r->left());
          }
          else
          {
            rule = r;
          }

          ExprVector actual_vars;
          expr::filter (rule, bind::IsVVar(), std::inserter (actual_vars, actual_vars.begin ()));
          //expr::filter (rule, bind::IsVar(), std::inserter (actual_vars, actual_vars.begin ()));
          if (actual_vars.size() == 0)
          {
            chcs.pop_back();
            continue;
          }

          assert(actual_vars.size() <= hr.locVars.size());

          ExprVector repl_vars;
          for (int i = 0; i < actual_vars.size(); i++)
          {
            string a1 = lexical_cast<string>(bind::name(actual_vars[i]));
            int ind = hr.locVars.size() - 1 - atoi(a1.substr(1).c_str());
            repl_vars.push_back(hr.locVars[ind]);
          }
          rule = replaceAll(rule, actual_vars, repl_vars);
        }

        if (isOpX<IMPL>(rule) && !isFapp(rule->right()) && !isOpX<FALSE>(rule->right()))
        {
          if (isOpX<TRUE>(rule->right()))
          {
            chcs.pop_back();
            continue;
          }
          rule = mk<IMPL>(mk<AND>(rule->left(), mk<NEG>(rule->right())), mk<FALSE>(m_efac));
        }

        if (!isOpX<IMPL>(rule)) rule = mk<IMPL>(mk<TRUE>(m_efac), rule);

        Expr body = rule->arg(0);
        Expr head = rule->arg(1);

        vector<ExprVector> origSrcSymbs;
        ExprSet lin;
        preprocess(body, hr.locVars, origSrcSymbs, hr.srcRelations, lin);
        if (hr.srcRelations.size() == 0)
        {
          if (hasUninterp(body))
          {
            outs () << "Unsupported format\n";
            outs () << "   " << *body << "\n";
            exit (0);
          }
        }

        hr.isFact = hr.srcRelations.empty();

        if (isOpX<FAPP>(head))
        {
          if (head->arg(0)->arity() == 2 && !hr.isFact)
          {
            addFailDecl(head->arg(0)->arg(0));
          }
          else
          {
            addDecl(head->arg(0));
          }
          hr.head = head->arg(0);
          hr.dstRelation = hr.head->arg(0);
        }
        else
        {
          if (!isOpX<FALSE>(head)) body = mk<AND>(body, mk<NEG>(head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.head = mk<FALSE>(m_efac);
          hr.dstRelation = mk<FALSE>(m_efac);
        }

        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelations.size() == 1 && hr.srcRelations[0] == hr.dstRelation);
        if (hr.isQuery) qCHCNum = chcs.size() - 1;

        ExprVector allOrigSymbs;
        for (auto & a : origSrcSymbs) for (auto & b : a) allOrigSymbs.push_back(b);
        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = head->args_begin()+1, end = head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
        }
        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());
        simplBoolReplCnj(allOrigSymbs, lin);
        hr.body = conjoin(lin, m_efac);
        vector<ExprVector> tmp;

        // we may have several applications of the same predicate symbol in the body:
        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          auto & a = hr.srcRelations[i];
          ExprVector tmp1;
          for (int j = 0; j < i; j++)
          {
            if (hr.srcRelations[i] == hr.srcRelations[j])
            {
              for (int k = 0; k < invVars[a].size(); k++)
              {
                Expr new_name = mkTerm<string> (varname + to_string(++total_var_cnt), m_efac);
                tmp1.push_back(cloneVar(invVars[a][k], new_name));
              }
              break;
            }
          }
          if (tmp1.empty())
          {
            tmp1 = invVars[a];
          }
          tmp.push_back(tmp1);
        }
        hr.assignVarsAndRewrite (origSrcSymbs, tmp,
                                 origDstSymbs, invVars[hr.dstRelation]);
        hr.body = simpleQE(hr.body, hr.locVars);

        // GF: ideally, hr.locVars should be empty after QE,
        // but the QE procedure is imperfect, so
        ExprVector body_vars;
        expr::filter (hr.body, bind::IsConst(), std::inserter (body_vars, body_vars.begin ()));
        for (auto it = hr.locVars.begin(); it != hr.locVars.end(); )
        {
          if (find(body_vars.begin(), body_vars.end(), *it) == body_vars.end())
            it = hr.locVars.erase(it);
          else ++it;
        }
      }

      for (int i = 0; i < chcs.size(); i++)
        incms[chcs[i].dstRelation].push_back(i);
    }

    void addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          outs () << "Multiple queries are not supported\n";
          exit(0);
        }
      }
    }

    Expr getPostcondition (int i, ExprVector& vars)
    {
      HornRuleExt& hr = chcs[i];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr.body, cnjs);
      ExprVector allVars = hr.locVars;
      for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());
      for (auto & a : cnjs)
      {
        if (emptyIntersect(a, allVars)) newCnjs.insert(a);
      }
      Expr res = conjoin(newCnjs, m_efac);
      return replaceAll(res, hr.dstVars, vars);
    }

    void slice (HornRuleExt* hr, vector<int>& varInds)
    {
      ExprSet cnjs;
      getConj(hr->body, cnjs);
      ExprSet newCnjs; // = cnjs;
      ExprSet deps;
      for (auto & i : varInds) deps.insert(hr->dstVars[i]);

      while (true)
      {
        ExprSet tmp;
        for (auto it = cnjs.begin(); it != cnjs.end(); ++it)
        {
          Expr c = *it;
          ExprSet vars0;
          filter (*it, bind::IsConst (), inserter(vars0, vars0.begin()));
          ExprSet vars1 = minusSets(vars0, deps);       // independent vars

          ExprSet vars3; // primed vars
          for (auto & a : vars0)
            if (find(hr->dstVars.begin(), hr->dstVars.end(), a) != hr->dstVars.end())
              vars3.insert(a);

          if (vars3.size() == 0)
          {
            tmp.insert(c);
            continue;
          }

          if (vars0.size() == vars1.size())
            continue;

          if (vars1.empty())
          {
            tmp.insert(c);
            continue;
          }

          ExprSet vars4; // unprimed vars
          ExprSet vars5; // primed vars
          for (auto & a : vars1)
            if (find(hr->dstVars.begin(), hr->dstVars.end(), a) == hr->dstVars.end())
              vars4.insert(a);
            else
              vars5.insert(a);

          if (vars5.size() != vars3.size())
          {
            tmp.insert(c);
            continue;
          }

          if (vars5.size() == 0)
          {
            tmp.insert(c);
            continue;
          }
        }
        newCnjs.insert(tmp.begin(), tmp.end());
        ExprSet deps2;
        filter (conjoin(newCnjs, m_efac), bind::IsConst (), inserter(deps2, deps2.begin()));

        for (auto & a : deps2)
          for (int i = 0; i < hr->srcVars.size(); i++)
            if (hr->dstRelation == hr->srcRelations[i])
              for (int j = 0; j < hr->srcVars[i].size(); j++)
                if (hr->srcVars[i][j] == a)
                  deps2.insert(hr->dstVars[j]);

        if (deps2.size() == deps.size()) break;
        deps = deps2;
      }

      hr->body = conjoin(newCnjs, m_efac);
    }

    void reCalculateIndexes(Expr r, vector<int>& varInds, ExprSet& vars)
    {
      for (auto & v : vars)
      {
        for (int i = 0; i < invVars[r].size(); i++)
        {
          if (invVars[r][i] == v)
          {
            varInds.push_back(i);
            break;
          }
        }
      }
    }

    void slice (Expr decl, vector<int>& varInds)
    {
      for (int i = incms[decl].size() - 1; i >= 0; i--)
      {
        HornRuleExt* hr = &chcs[incms[decl][i]];
        if (varInds.empty())
        {
          ExprSet vars;
          filter (hr->body, bind::IsConst(), std::inserter (vars, vars.begin ()));
          for (auto & r : hr->srcRelations)
          {
            reCalculateIndexes(r, varInds, vars);
            slice(r, varInds);
          }
        }
        else
        {
          // one level only, for now; to extend
          slice(hr, varInds);
          ExprSet vars;
          filter (hr->body, bind::IsConst(), std::inserter (vars, vars.begin ()));
          reCalculateIndexes(decl, varInds, vars);
        }
      }
    }

    void slice ()
    {
      vector<int> varInds;
      slice(failDecl, varInds);
    }

    void print() const
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs){
        if (hr.isFact) outs() << "  INIT:\n";
        if (hr.isInductive) outs() << "  TRANSITION RELATION:\n";
        if (hr.isQuery) outs() << "  BAD:\n";

        outs () << "    ";

        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          outs () << * hr.srcRelations[i];
          outs () << " (";
          for(auto &a: hr.srcVars[i]) outs() << *a << ", ";
            outs () << "\b\b)";
          outs () << " /\\ ";
        }
        outs () << "\b\b\b\b -> " << * hr.dstRelation;

        if (hr.dstVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.dstVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        outs() << "\n    body: " << * hr.body << "\n";
      }
    }

    ZFixedPoint<EZ3> toZ3fp()
    {
      // fixed-point object
      ZFixedPoint<EZ3> fp (m_z3);
      ZParams<EZ3> params (m_z3);
      fp.set (params);

      Expr errRel = bind::boolConstDecl(failDecl);
      fp.registerRelation(errRel);

      for (auto & dcl : decls) fp.registerRelation (dcl);

      for (auto & r : chcs)
      {
        ExprSet allVars;
        for (const auto& srcVars : r.srcVars) {
          allVars.insert(srcVars.begin(), srcVars.end());
        }
        allVars.insert(r.dstVars.begin(), r.dstVars.end());
        allVars.insert(r.locVars.begin(), r.locVars.end());

        if (r.isQuery)
        {
          r.head = bind::fapp (errRel);
        }
        else
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.dstRelation)
            {
              r.head = bind::fapp (dcl, r.dstVars);
              break;
            }
          }
        }

        ExprSet pres;
        if (!r.isFact)
        {
          int counter = 0;
          for (const auto srcRelation : r.srcRelations) {
            for (auto & dcl : decls)
            {
              if (dcl->left() == srcRelation)
              {
                pres.insert(bind::fapp (dcl, r.srcVars[counter]));
                break;
              }
            }
            ++counter;
          }
        }
        getConj(r.body, pres);
        assert(isOpX<FAPP>(r.head));
        fp.addRule(allVars, boolop::limp (conjoin(pres, m_efac), r.head));
      }
      fp.addQuery(bind::fapp(bind::fdecl(this->failDecl, ExprVector{sort::boolTy(m_efac)})));
      return fp;
    }

    void dump(std::ostream& out)
    {
      auto fp = toZ3fp();
      out << fp << std::endl;
    }

    ExprMap solve(unsigned timeout = 0u) {
      auto fp = toZ3fp();
      ZParams<EZ3> params (m_z3);
      params.set("timeout", timeout);
      fp.set (params);
      tribool res;
      ExprMap solution;
      try {
        res = fp.query();
      } catch (z3::exception &e){
        std::string msg = e.msg();
        if (msg.find("canceled") == std::string::npos) {
          outs() << "Z3 ex: " << e.msg() << "...\n";
          exit(55);
        }
        else {
          // timeout
          return solution;
        }
      }
      if (!res) {
        for (auto const &pred : decls) {
          auto it = invVars.find(bind::name(pred));
          assert(it != invVars.end());
          Expr lemma = fp.getCoverDelta(bind::fapp(pred, it->second));
          solution.insert(std::make_pair<>(pred, lemma));
        }
      }
      return solution;
    }

    void simplifyCHCSystemSyntactically() {
      for (auto & chc : chcs) {
        chc.body = simplifyExpressionSyntactically(chc.body);
      }
    }

    Expr simplifyExpressionSyntactically(Expr e) {
      Expr res = simplifyBool(e);
      if (hasBV) {
        return simplifyBVConstructs(res);
      }
      return res;
    }

    Expr simplifyBVConstructs(Expr e) {
      std::map<Expr, unsigned> bitwidths;
      RW<SimplifyBVExpr> rw (new SimplifyBVExpr(e->getFactory(), bitwidths));
      return dagVisit(rw, e);
    }

    void strengthenWithInvariants(ExprMap const& invariants) {
      for (auto & chc: this->chcs) {
        // inspiration from check CHC
        ExprSet newBody;
        newBody.insert(chc.body);
        for (int i = 0; i < chc.srcRelations.size(); i++)
        {
          Expr rel = chc.srcRelations[i];
          ExprSet lms = {invariants.at(rel)};
          Expr substInvariants = replaceAll(conjoin(lms, m_efac), this->invVars[rel], chc.srcVars[i]);
          getConj(substInvariants, newBody);
        }
        if (!chc.isQuery)
        {
          Expr rel = chc.dstRelation;
          Expr lms = invariants.at(rel);
          Expr substInvariants = replaceAll(lms, this->invVars[rel], chc.dstVars);
          getConj(substInvariants, newBody);
        }
        chc.body = conjoin(newBody, this->m_efac);
      }

    }
  };
}
#endif
