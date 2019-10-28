#ifndef CANDCHECKER__HPP__
#define CANDCHECKER__HPP__

#include "ae/SMTUtils.hpp"
#include "Horn.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class CandChecker
  {
    private:

    ExprFactory &efac;
    EZ3 z3;
    ufo::ZSolver<ufo::EZ3> smt_solver;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    ExprVector& vars;
    ExprSet learnedExprs;

    public:
    
    CandChecker (ExprFactory &_efac, HornRuleExt* _fc, HornRuleExt* _tr, HornRuleExt* _qr) :
      efac(_efac), z3(efac), smt_solver (z3), fc(_fc), tr(_tr), qr(_qr), vars(qr->srcVars)
    {
      // sanity checks:
      assert (fc != NULL);
      assert (tr != NULL);
      assert (qr != NULL);
      for (int i = 0; i < tr->srcVars.size(); i++)
        assert (tr->srcVars[i] == vars[i]);
      for (int i = 0; i < tr->dstVars.size(); i++)
        assert (tr->dstVars[i] == fc->dstVars[i]);
    }

    Expr getModel(ExprVector& vars)
    {
      // used to explain the reason why some of the check failed
      // i.e., it is supposed to be called after "smt_solver.solve()" returned SAT

      ExprVector eqs;
      ZSolver<EZ3>::Model m = smt_solver.getModel();
      for (auto & v : vars)
        if (v != m.eval(v))
            eqs.push_back(mk<EQ>(v, m.eval(v)));
      return conjoin (eqs, efac);
    }

    Expr getlearnedLemmas()
    {
      return conjoin (learnedExprs, efac);
    }

    bool checkInitiation(Expr cand)
    {
      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        cand = replaceAll(cand, vars[j], fc->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (fc->body);
      smt_solver.assertExpr (mk<NEG>(cand));

      return (bool)(!smt_solver.solve ());
    }

    bool checkInductiveness(Expr cand)
    {
      // supposed to be called after checkInitiation

      Expr candPrime = cand;

      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        candPrime = replaceAll(candPrime, vars[j], tr->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (tr->body);
      smt_solver.assertExpr (cand);
      smt_solver.assertExpr (getlearnedLemmas()); // IMPORTANT: use all lemmas learned so far
      smt_solver.assertExpr (mk<NEG>(candPrime));

      bool res = (bool)!smt_solver.solve ();
      if (res) learnedExprs.insert (cand);  // inductiveness check passed; so add a new lemma

      return res;
    }

    bool checkSafety()
    {
      // supposed to be called after checkInductiveness
      // but it does not take a candidate as input since it is already in learnedExprs

      smt_solver.reset();
      smt_solver.assertExpr (qr->body);
      smt_solver.assertExpr (getlearnedLemmas());

      return (bool)!smt_solver.solve ();
    }

    void serializeInvars()
    {
      Expr lms = getlearnedLemmas();
      for (auto & a : qr->origNames) lms = replaceAll(lms, a.first, a.second);

      smt_solver.reset();
      smt_solver.assertExpr(lms);

      smt_solver.toSmtLib (errs());
      errs().flush ();
    }

  };
  
  inline void simpleCheck(const char * chcfile, unsigned bw_bound, unsigned bval_bound, bool enable_eqs, bool enable_adds, bool enable_bvnot, bool enable_extract, bool enable_concr, bool enable_concr_impl, bool enable_or)
  {

    if (!enable_eqs) // currently, `enable_adds` and `enable_extract` depend on `enable_eqs`
    {
      enable_adds = 0;
      enable_extract = 0;
    }

    outs () << "Max bitwidth considered: " << bw_bound << "\n"
            << "Max concrete values considered: " << bval_bound << "\n"
            << "Equalities (between variables) enabled: " << enable_eqs << "\n"
            << "Bitwise additions enabled: " << enable_adds << "\n"
            << "Bitwise negations enabled: " << enable_bvnot << "\n"
            << "Bit extraction enabled (in equalities): " << enable_extract << "\n"
            << "Concrete values enabled (in equalities): " << enable_concr << "\n"
            << "Implications using equalities and concrete values enabled: " << enable_concr_impl << "\n"
            << "Disjunctions among (subsets of) various equalities enabled: " << enable_or << "\n";

    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(string(chcfile));
    Expr cand = mk<TRUE>(efac);

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    for (auto & a : ruleManager.chcs)
      if (a.isInductive) tr = &a;
      else if (a.isFact) fc = &a;
      else if (a.isQuery) qr = &a;

    CandChecker cc(efac, fc, tr, qr);

    ExprSet cands;

    // get inv vars
    map<int, ExprVector> bvVars;
    map<int, Expr> bitwidths;
    set<int> bitwidths_int;
    for (auto & a: tr->srcVars)
    {
      if (bv::is_bvconst(a))
      {
        unsigned bw = bv::width(a->first()->arg(1));
        bitwidths_int.insert(bw);
        bitwidths[bw] = a->first()->arg(1);
        bvVars[bw].push_back(a);
      }
    }

    ExprVector eqs1;
    ExprVector eqs2;

    if (enable_eqs)
    {
      for (int i : bitwidths_int)
      {
        if (i > bw_bound) continue; // limit
        for (int j = 0; j < bvVars[i].size(); j++)
        {
          for (int k = j + 1; k < bvVars[i].size(); k++)
          {
            Expr tmp = mk<EQ>(bvVars[i][j], bvVars[i][k]);
            eqs1.push_back(tmp);
            if (enable_bvnot)
            {
              eqs1.push_back(tmp);
              eqs1.push_back(mk<EQ>(bvVars[i][j], mk<BNOT>(bvVars[i][k])));
            }
            if (enable_adds)
            {
              for (int l = 0; l < bvVars[i].size(); l++)
              {
                if (l == k || l == j) continue;
                Expr tmp = mk<EQ>(bvVars[i][l], mk<BADD>(bvVars[i][j], bvVars[i][k]));
                eqs1.push_back(tmp);
              }
            }
          }
          if (enable_extract)
          {
            for (int i1 = i + 1; i1 <= bw_bound; i1++)
            {
              for (int j1 = 0; j1 < bvVars[i1].size(); j1++)
              {
                eqs1.push_back(mk<EQ>(bvVars[i][j], bv::extract(i-1, 0, bvVars[i1][j1])));
              }
            }
          }
        }
      }
    }

    if (enable_concr)
    {
      for (int i : bitwidths_int)
      {
        if (i > bw_bound) continue; // limit
        for (auto & a : bvVars[i])
        {
          for (int j = 0; j <= bval_bound && j < pow(2, i); j++)
          {
            Expr tmp = bv::bvnum(j, bv::width(bitwidths[i]), efac);
            eqs2.push_back(mk<EQ>(a, tmp));
            if (enable_bvnot)
              eqs2.push_back(mk<EQ>(mk<BNOT>(a), tmp));
          }
        }
      }

      if (enable_concr_impl)
        for (auto & a : eqs2)
          for (auto & b : eqs2)
            if (a->left() != b->left())
              cands.insert(mk<IMPL>(a, b));

    }

    if (enable_or)
      for (auto & c : eqs1)
        for (auto & d : eqs2)
          if (c != d)
            cands.insert(mk<OR>(c, d));

    if (cands.empty())
    {
      cands.insert(eqs1.begin(), eqs1.end());
      cands.insert(eqs2.begin(), eqs2.end());
    }

    int iter = 0;
    for (auto & cand : cands)
    {
      iter++;
      if (cc.checkInitiation(cand) &&
          cc.checkInductiveness(cand) &&
          cc.checkSafety())
      {
        outs () << "proved\n";
        outs () << "iter: " << iter << " / " << cands.size() << "\n";
        cc.serializeInvars();
        return;
      }
    }
    outs () << "unknown\n";
  }
}

#endif
