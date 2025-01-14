#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearner.hpp"

#ifdef HAVE_ARMADILLO
#include "DataLearner.hpp"
#endif

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV3 : public RndLearnerV2
  {
    private:

    ExprSet checked;
    map<int, ExprVector> candidates;
    int updCount = 1;

    map<int, Expr> iterators; // per cycle
    map<int, Expr> preconds;
    map<int, Expr> postconds;
    map<int, Expr> ssas;
    map<int, ExprSet> qvars;
    map<int, bool> iterGrows;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, bool freqs, bool aggp) :
      RndLearnerV2 (efac, z3, r, freqs, aggp){}

    bool checkInit(int invNum, Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isFact && hr.dstRelation == rel)
        {
          adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    bool checkInductiveness(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        bool checkedSrc = find(checked.begin(), checked.end(), hr.srcRelation) != checked.end();
        bool checkedDst = find(checked.begin(), checked.end(), hr.dstRelation) != checked.end();
        if ((hr.srcRelation == rel && hr.dstRelation == rel) ||
            (hr.srcRelation == rel && checkedDst) ||
            (hr.dstRelation == rel && checkedSrc) ||
            (checkedSrc && checkedDst) ||
            (hr.isFact && checkedDst))
        {
          if (!hr.isQuery) adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    Expr renameCand(Expr newCand, ExprVector& varsRenameFrom, int invNum)
    {
      for (auto & v : invarVars[invNum])
        newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
      return newCand;
    }

    Expr eliminateQuantifiers(Expr formula, ExprVector& varsRenameFrom, int invNum)
    {
      ExprSet allVars;
      ExprSet quantified;
      ExprSet forallQuantified;
      getQuantifiedVars(formula, forallQuantified);
      expr::filter (formula, bind::IsConst(), std::inserter (allVars, allVars.begin ()));
      for (auto & v : allVars)
        if (find(varsRenameFrom.begin(), varsRenameFrom.end(), v) == varsRenameFrom.end())
          if (find(forallQuantified.begin(), forallQuantified.end(), v) == forallQuantified.end())
            quantified.insert(v);

      if (containsOp<FORALL>(formula))
      {
        Expr newCand = simpleQE(formula, quantified, true);
        ExprSet ops;
        getConj(newCand, ops);
        for (auto & a : ops)
        {
          if (isOpX<FORALL>(a))
          {
            newCand = a;
            break;
          }
        }
        return renameCand(newCand, varsRenameFrom, invNum);
      }

      if (findNonlin(formula) || findArray(formula) || containsOp<IDIV>(formula) || containsOp<MOD>(formula))
      {
        Expr newCand = simpleQE(formula, quantified, true, true);
        return renameCand(newCand, varsRenameFrom, invNum);
      }

      AeValSolver ae(mk<TRUE>(m_efac), formula, quantified);
      if (ae.solve())
      {
        Expr newCand = ae.getValidSubset();
        return renameCand(newCand, varsRenameFrom, invNum);
      }
      return mk<TRUE>(m_efac);
    }

    void addPropagatedArrayCands(Expr rel, int invNum, Expr candToProp)
    {
      vector<int> tmp;
      ruleManager.getCycleForRel(rel, tmp);
      if (tmp.size() != 1) return; // todo: support

      Expr fls = replaceAll(candToProp->last()->right(),
                            *arrAccessVars[invNum].begin(), iterators[invNum]);
      Expr bdy = rewriteSelectStore(ruleManager.chcs[tmp[0]].body);

      ExprVector ev;
      for (int h = 0; h < ruleManager.chcs[tmp[0]].dstVars.size(); h++)
      {
        Expr var = ruleManager.chcs[tmp[0]].srcVars[h];
        if (iterators[invNum] == var)
          ev.push_back(iterators[invNum]);
        else
          ev.push_back(ruleManager.chcs[tmp[0]].dstVars[h]);
      }

      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(fls, cnjs);
      getConj(bdy, cnjs);
      for (auto & a : cnjs) // hack
      {
        if (isOpX<EQ>(a) && bind::isConst<ARRAY_TY>(a->left()) && bind::isConst<ARRAY_TY>(a->right()))
          continue;
        newCnjs.insert(a);
      }
      ExprMap mp;
      bdy = replaceSelects(conjoin(newCnjs, m_efac), mp);
      for (auto & a : mp)
      {
        if (!emptyIntersect(a.first, ruleManager.chcs[tmp[0]].dstVars))
        {
          ev.push_back(a.second);
        }
      }

      Expr newCand2;
      cnjs.clear();
      getConj(eliminateQuantifiers(bdy, ev, invNum), cnjs);
      for (auto & c : cnjs)
      {
        Expr e = ineqNegReverter(c);
        if (isOp<ComparissonOp>(e))
        {
          for (auto & a : mp) e = replaceAll(e, a.second, a.first);
          if (findArray(e) && !emptyIntersect(iterators[invNum], e))
          {
            e = replaceAll(e, iterators[invNum], *arrAccessVars[invNum].begin());
            e = renameCand(e, ruleManager.chcs[tmp[0]].dstVars, invNum);

            // workaround: it works only during bootstrapping now
            arrCands[invNum].insert(e);
          }
        }
      }
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, Expr relFrom, ExprVector& varsRenameFrom, Expr rel, bool seed, bool fwd)
    {
      Expr formula = mk<AND>(candToProp, constraint);
      if (!containsOp<FORALL>(candToProp) && !u.isSat(formula)) return false; // sometimes, maybe we should return true.

      int invNum = getVarIndex(rel, decls);
      Expr newCand;

      if (containsOp<FORALL>(candToProp))
      {
        // GF: not tested for backward propagation
        if (fwd == false) return true;
        if (finalizeArrCand(candToProp, constraint, relFrom))
        {
          addPropagatedArrayCands(rel, invNum, candToProp);
          newCand = eliminateQuantifiers(mk<AND>(candToProp, constraint), varsRenameFrom, invNum);
          // GF: temporary workaround:
          // need to support Houdini for arrays, to be able to add newCand and newCand1 at the same time
          Expr newCand1 = replaceArrRangeForIndCheck(invNum, newCand, true);
          auto candsTmp = candidates;
          candidates[invNum].push_back(newCand);
          bool res0 = checkCand(invNum);
          if (!candidates[invNum].empty()) return res0;
          candidates = candsTmp;
          candidates[invNum].push_back(newCand1);
          return checkCand(invNum);
        }
        else
        {
          // very ugly at the moment, to be revisited
          newCand = eliminateQuantifiers(mk<AND>(candToProp, constraint), varsRenameFrom, invNum);
          candidates[invNum].push_back(newCand);
          return checkCand(invNum);
        }
      }

      ExprSet dsjs;
      getDisj(candToProp, dsjs);
      ExprSet newSeedDsjs;
      for (auto & d : dsjs)
      {
        Expr r = eliminateQuantifiers(mk<AND>(d, constraint), varsRenameFrom, invNum);
        newSeedDsjs.insert(r);
      }
      newCand = disjoin(newSeedDsjs, m_efac);

      if (seed)
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(newCand, cnjs);
        for (auto & cnd : cnjs)
        {
          newCnjs.insert(cnd);
          addCandidate(invNum, cnd);
        }

        newCand = conjoin(newCnjs, m_efac);
        if (isOpX<TRUE>(newCand)) return true;
        else return propagate(invNum, newCand, true);
      }
      else
      {
        ExprSet cnjs;
        getConj(newCand, cnjs);
        for (auto & a : cnjs) addCandidate(invNum, a);
        return checkCand(invNum);
      }
    }

    bool addCandidate(int invNum, Expr cnd)
    {
      SamplFactory& sf = sfs[invNum].back();
      Expr allLemmas = sf.getAllLemmas();
      if (containsOp<FORALL>(cnd) || containsOp<FORALL>(allLemmas))
      {
        if (containsOp<FORALL>(cnd))
        {
          auto hr = ruleManager.getFirstRuleOutside(decls[invNum]);
          assert(hr != NULL);

          ExprSet cnjs;
          ExprSet newCnjs;
          Expr it = iterators[invNum];
          if (it != NULL) cnd = replaceArrRangeForIndCheck (invNum, cnd);
        }
        candidates[invNum].push_back(cnd);
        return true;
      }
      if (!isOpX<TRUE>(allLemmas) && u.implies(allLemmas, cnd)) return false;

      for (auto & a : candidates[invNum])
      {
        if (u.isEquiv(a, cnd)) return false;
      }
      candidates[invNum].push_back(cnd);
      return true;
    }

    bool finalizeArrCand(Expr& cand, Expr constraint, Expr relFrom)
    {
      // only forward currently
      if (!isOpX<FORALL>(cand)) return false;
      if (!findArray(cand)) return false;

      // need to make sure the candidate is finalized (i.e., not a nested loop)
      int invNum = getVarIndex(relFrom, decls);
      if (u.isSat(postconds[invNum], constraint)) return false;

      cand = replaceAll(cand, cand->last()->left(), conjoin(arrIterRanges[invNum], m_efac));
      return true;
    }

    Expr replaceArrRangeForIndCheck(int invNum, Expr cand, bool fwd = false)
    {
      Expr itRepl = iterators[invNum];
      Expr post = postconds[invNum];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(cand->last()->left(), cnjs);

      // TODO: support the case when there are two or more quantified vars

      Expr it = bind::fapp(cand->arg(0));
      ExprSet extr;
      if      (iterGrows[invNum] && fwd)   extr.insert(mk<GEQ>(it, itRepl));
      else if (iterGrows[invNum] && !fwd)   extr.insert(mk<LT>(it, itRepl));
      else if (!iterGrows[invNum] && fwd)  extr.insert(mk<LEQ>(it, itRepl));
      else if (!iterGrows[invNum] && !fwd)  extr.insert(mk<GT>(it, itRepl));

      extr.insert(cand->last()->left());
      return replaceAll(cand, cand->last()->left(), conjoin(extr, m_efac));
    }

    bool propagate(int invNum, Expr cand, bool seed)
    {
      bool res = true;
      Expr rel = decls[invNum];

      checked.insert(rel);
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.srcRelation == hr.dstRelation || hr.isQuery) continue;

        SamplFactory* sf1;
        SamplFactory* sf2;

        // adding lemmas to the body. GF: disabled because something is wrong with them and arrays
        Expr constraint = hr.body;
        sf2 = &sfs[getVarIndex(hr.dstRelation, decls)].back();
//        Expr lm2 = sf2->getAllLemmas();
//        for (auto & v : invarVars[getVarIndex(hr.dstRelation, decls)])
//          lm2 = replaceAll(lm2, v.second, hr.dstVars[v.first]);
//        constraint = mk<AND>(constraint, lm2);

        if (!hr.isFact)
        {
          sf1 = &sfs[getVarIndex(hr.srcRelation, decls)].back();
//          constraint = mk<AND>(constraint, sf1->getAllLemmas());
        }

        // forward:
        if (hr.srcRelation == rel && find(checked.begin(), checked.end(), hr.dstRelation) == checked.end())
        {
          Expr replCand = cand;
          for (int i = 0; i < 3; i++) for (auto & v : sf1->lf.nonlinVars) replCand = replaceAll(replCand, v.second, v.first);
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.srcVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.dstVars, hr.dstRelation, seed, true);
        }

        // backward (very similarly):
        if (hr.dstRelation == rel && find(checked.begin(), checked.end(), hr.srcRelation) == checked.end() && !hr.isFact)
        {
          Expr replCand = cand;
          for (int i = 0; i < 3; i++) for (auto & v : sf2->lf.nonlinVars) replCand = replaceAll(replCand, v.second, v.first);
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.dstVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.srcVars, hr.srcRelation, seed, false);
        }
      }
      return res;
    }

    bool checkCand(int invNum)
    {
      Expr rel = decls[invNum];
      if (!checkInit(invNum, rel)) return false;
      if (!checkInductiveness(rel)) return false;

      return propagate(invNum, conjoin(candidates[invNum], m_efac), false);
    }

    // a simple method to generate properties of a larger Array range, given already proven ranges
    void generalizeArrInvars (SamplFactory& sf)
    {
      if (sf.learnedExprs.size() > 1)
      {
        ExprVector posts;
        ExprVector pres;
        map<Expr, ExprVector> tmp;
        ExprVector tmpVars;
        ExprVector arrVars;
        Expr tmpIt = bind::intConst(mkTerm<string> ("_tmp_it", m_efac));

        for (auto & a : sf.learnedExprs)
        {
          if (!isOpX<FORALL>(a)) continue;
          Expr learnedQF = a->last();
          if (!isOpX<IMPL>(learnedQF)) continue;
          ExprVector se;
          filter (learnedQF->last(), bind::IsSelect (), inserter(se, se.begin()));

          // filter out accesses via non-quantified indeces
          for (auto it = se.begin(); it != se.end();)
          {
            bool found = false;
            for (int i = 0; i < a->arity(); i++)
            {
              if (contains(se[0]->right(), a->arg(0)))
              {
                found = true;
                break;
              }
            }
            if (!found) it = se.erase(it);
            else ++it;
          }

          bool multipleIndex = false;
          for (auto & s : se) {
            if (se[0]->right() != s->right()) {
              multipleIndex = true;
              break;
            }
          }

          if (se.size() == 0 || multipleIndex) continue;

          if (arrVars.size() == 0) {
            for (int index = 0; index < se.size(); index++) {
              arrVars.push_back(se[index]->left());
              tmpVars.push_back(bind::intConst(mkTerm<string> ("_tmp_var_" + lexical_cast<string>(index), m_efac)));
            }
          } else {
            bool toContinue = false;
            for (auto & s : se) {
              if (find(arrVars.begin(), arrVars.end(), s->left()) == arrVars.end()) {
                toContinue = true;
                break;
              }
            }
            if (toContinue) continue;
          }

          Expr postReplaced = learnedQF->right();
          for (int index = 0; index < se.size() && index < tmpVars.size(); index++)
          postReplaced = replaceAll(postReplaced, se[index], tmpVars[index]);

          ExprSet postVars;
          filter(postReplaced, bind::IsConst(), inserter(postVars, postVars.begin()));
          for (auto & fhVar : sf.lf.getVars()) postVars.erase(fhVar);
          for (auto & tmpVar : tmpVars) postVars.erase(tmpVar);
          if (postVars.size() > 0)
          {
            AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(postReplaced, mk<EQ>(tmpIt, se[0]->right())), postVars);
            if (ae.solve())
            {
              Expr pr = ae.getValidSubset();
              ExprSet conjs;
              getConj(pr, conjs);
              if (conjs.size() > 1)
              {
                for (auto conjItr = conjs.begin(); conjItr != conjs.end();)
                {
                  ExprVector conjVars;
                  filter (*conjItr, bind::IsConst(), inserter(conjVars, conjVars.begin()));
                  bool found = false;
                  for (auto & conjVar : conjVars)
                  {
                    if (find (tmpVars.begin(), tmpVars.end(), conjVar) != tmpVars.end())
                    {
                      found = true;
                      break;
                    }
                  }
                  if (!found) conjItr = conjs.erase(conjItr);
                  else ++conjItr;
                }
              }
              postReplaced = conjoin(conjs, m_efac);
            }
          }

          pres.push_back(learnedQF->left());
          posts.push_back(postReplaced);
          tmp[mk<AND>(learnedQF->left(), postReplaced)].push_back(se[0]->right());
        }

        if (tmp.size() > 0)
        {
          for (auto & a : tmp)
          {
            if (a.second.size() > 1)
            {
              Expr disjIts = mk<FALSE>(m_efac);
              for (auto & b : a.second) disjIts = mk<OR>(disjIts, mk<EQ>(tmpIt, b));
              ExprSet elementaryIts;
              filter (disjIts, bind::IsConst (), inserter(elementaryIts, elementaryIts.begin()));
              for (auto & a : sf.lf.getVars()) elementaryIts.erase(a);
              elementaryIts.erase(tmpIt);
              if (elementaryIts.size() == 1)
              {
                AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(disjIts, a.first->left()), elementaryIts);
                if (ae.solve())
                {
                  ExprVector args;
                  Expr it = *elementaryIts.begin();
                  args.push_back(it->left());
                  Expr newPre = replaceAll(ae.getValidSubset(), tmpIt, it);
                  Expr newPost = replaceAll(a.first->right(), tmpIt, it);
                  for (int index = 0; index < tmpVars.size() && index < arrVars.size(); index++)
                  newPost = replaceAll(newPost, tmpVars[index], mk<SELECT>(arrVars[index], it));
                  args.push_back(mk<IMPL>(newPre, newPost));
                  Expr newCand = mknary<FORALL>(args);
                  sf.learnedExprs.insert(newCand);
                }
              }
            }
          }
        }
      }
    }

    void assignPrioritiesForLearned()
    {
//      bool progress = true;
      for (auto & cand : candidates)
      {
        if (cand.second.size() > 0)
        {
          SamplFactory& sf = sfs[cand.first].back();
          for (auto & b : cand.second)
          {
            if (containsOp<FORALL>(b))
            {
              sf.learnedExprs.insert(b);
            }
            else
            {
              ExprVector invVars;
              for (auto & a : invarVars[cand.first]) invVars.push_back(a.second);
              Expr learnedCand = normalizeDisj(b, invVars);
              Sampl& s = sf.exprToSampl(learnedCand);
              sf.assignPrioritiesForLearned();
              if (!u.implies(sf.getAllLemmas(), learnedCand))
                sf.learnedExprs.insert(learnedCand);
            }
//            else progress = false;
          }
        }
      }
//            if (progress) updateGrammars(); // GF: doesn't work great :(
    }

    bool synthesize(int maxAttempts, char * outfile)
    {
      ExprSet cands;
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        int tmp = ruleManager.cycles[i % ruleManager.cycles.size()][0];
        int invNum = getVarIndex(ruleManager.chcs[tmp].srcRelation, decls);
        checked.clear();
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand = sf.getFreshCandidate(i < 25); // try simple array candidates first
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
//        outs () << " - - - sampled cand: #" << i << ": " << *cand << "\n";

        if (!addCandidate(invNum, cand)) continue;
        if (checkCand(invNum))
        {
          assignPrioritiesForLearned();
          generalizeArrInvars(sf);
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations\n";
            return true;
          }
        }
      }
      return false;
    }

    bool splitUnsatSets(ExprVector & src, ExprVector & dst1, ExprVector & dst2)
    {
      if (u.isSat(src)) return false;

      for (auto & a : src) dst1.push_back(a);

      for (auto it = dst1.begin(); it != dst1.end(); )
      {
        dst2.push_back(*it);
        it = dst1.erase(it);
        if (u.isSat(dst1)) break;
      }

      // now dst1 is SAT, try to get more things from dst2 back to dst1

      for (auto it = dst2.begin(); it != dst2.end(); )
      {
        if (!u.isSat(conjoin(dst1, m_efac), *it)) { ++it; continue; }
        dst1.push_back(*it);
        it = dst2.erase(it);
      }

      return true;
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          for (auto & hr : ruleManager.chcs)
          {
            if (hr.dstRelation == decls[i]) worklist.push_back(&hr);
          }
        }
      }

      // basically, just checks initiation and immediately removes bad candidates
      multiHoudini(worklist, false);

      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          u.splitUnsatSets(candidates[i], tmp, stub);
          candidates[i] = tmp;
        }
      }

      return true;
    }

    bool hasQuantifiedCands(map<int, ExprVector>& cands)
    {
      for (auto & a : cands)
      {
        for (auto & b : a.second)
        {
          if (isOpX<FORALL>(b)) return true;
        }
      }
      return false;
    }

    bool multiHoudini(vector<HornRuleExt*> worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;
      map<int, ExprVector> candidatesTmp = candidates;
      bool res1 = true;
      for (auto &h: worklist)
      {
        HornRuleExt& hr = *h;

        if (hr.isQuery) continue;

        if (!checkCHC(hr, candidatesTmp))
        {
          bool res2 = true;
          int ind = getVarIndex(hr.dstRelation, decls);
          Expr model = u.getModel(hr.dstVars);
          if (model == NULL || hasQuantifiedCands(candidatesTmp))
          {
            // something went wrong with z3. do aggressive weakening (TODO: try bruteforce):
            candidatesTmp[ind].clear();
            res2 = false;
          }
          else
          {
            ExprVector& ev = candidatesTmp[ind];
            ExprVector invVars;
            for (auto & a : invarVars[ind]) invVars.push_back(a.second);
            SamplFactory& sf = sfs[ind].back();

            for (auto it = ev.begin(); it != ev.end(); )
            {
              Expr repl = *it;
              for (auto & v : invarVars[ind]) repl = replaceAll(repl, v.second, hr.dstVars[v.first]);

              if (!u.isSat(model, repl))
              {
                if (hr.isFact)
                {
                  Expr failedCand = normalizeDisj(*it, invVars);
//                outs () << "failed cand for " << *hr.dstRelation << ": " << *failedCand << "\n";
                  Sampl& s = sf.exprToSampl(failedCand);
                  sf.assignPrioritiesForFailed();
                }
                it = ev.erase(it);
                res2 = false;
              }
              else
              {
                ++it;
              }
            }
          }

          if (recur && !res2)
          {
            res1 = false;
            break;
          }
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool findInvVar(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));

      for (auto & v : vars)
      {
        bool found = false;
        for (auto & w : invarVars[invNum])
        {
          if (w.second == v)
          {
            found = true;
            break;
          }
        }
        if (!found)
        {
          if (find (ve.begin(), ve.end(), v) == ve.end())
            return false;
        }
      }
      return true;
    }

    bool toCont(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));
      bool toCont = true;
      for (auto & expr : vars)
      {
        if (!findInvVar(invNum, expr, ve))
        {
          toCont = false;
          break;
        }
      }
      return toCont;
    }

    // heuristic to instantiate a quantified candidate for some particular instances
    void createGroundInstances (ExprSet& vals, ExprSet& res, Expr qcand, Expr iterVar)
    {
      ExprSet se;
      filter (qcand, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & a : se)
      {
        if (iterVar == a->right())
        {
          for (auto & v : vals)
          {
            res.insert(replaceAll(qcand, iterVar, v));
          }
        }
      }
    }

    // heuristic to replace weird variables in candidates
    bool prepareArrCand (Expr& replCand, ExprMap& replLog, ExprVector& av,
                         ExprSet& tmpRanges, ExprSet& concreteVals, int ind, int i = 0)
    {
      if (av.empty()) return false;

      ExprSet se;
      filter (replCand, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & a : se)
      {
        if (isOpX<MPZ>(a->right())  || (!findInvVar(ind, a->right(), av)))
        {
          if (isOpX<MPZ>(a->right()))
          {
            tmpRanges.insert(mk<EQ>(av[i], a->right()));
            concreteVals.insert(a->right());
          }
          // TODO:  try other combinations of replacements
          if (i >= av.size()) return false;
          replLog[a->right()] = av[i];
          replCand = replaceAll(replCand, a->right(), replLog[a->right()]);

          return prepareArrCand (replCand, replLog, av, tmpRanges, concreteVals, ind, i + 1);
        }
      }
      return true;
    }

    // adapted from doSeedMining
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands, bool analizeCode = true)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      ExprSet candsFromCode;
      bool analizedExtras = false;
      bool isFalse = false;

      // for Arrays
      ExprSet tmpArrAccess;
      ExprSet tmpArrSelects;
      ExprSet tmpArrCands;
      ExprSet tmpArrFuns;
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;

        SeedMiner sm (hr, invRel, invarVars[ind], sf.lf.nonlinVars);
        if (analizeCode) sm.analizeCode();
        else sm.candidates.clear();
        if (!analizedExtras && hr.srcRelation == invRel)
        {
          sm.analizeExtras (cands[invRel]);
          analizedExtras = true;
        }

        for (auto &cand : sm.candidates) candsFromCode.insert(cand);

        // for arrays
        if (analizeCode && ruleManager.hasArrays)
        {
          tmpArrCands.insert(sm.arrCands.begin(), sm.arrCands.end());
          tmpArrSelects.insert(sm.arrSelects.begin(), sm.arrSelects.end());
          tmpArrFuns.insert(sm.arrFs.begin(), sm.arrFs.end());
        }
      }

      if (ruleManager.hasArrays)
      {
        if (preconds[ind] != NULL)
        {
          Expr qVar = bind::intConst(mkTerm<string> ("_FH_arr_it", m_efac));
          arrAccessVars[ind].push_back(qVar);

          assert (isOpX<EQ>(preconds[ind])); // TODO: support more

          ExprVector invAndIterVarsAll;
          for (auto & a : invarVars[ind]) invAndIterVarsAll.push_back(a.second);
          invAndIterVarsAll.push_back(qVar);

          Expr fla;
          if (preconds[ind]->right() == iterators[ind])
            fla = (iterGrows[ind]) ? mk<GEQ>(qVar, preconds[ind]->left()) :
                                     mk<LEQ>(qVar, preconds[ind]->left());
          else if (preconds[ind]->left() == iterators[ind])
            fla = (iterGrows[ind]) ? mk<GEQ>(qVar, preconds[ind]->right()) :
                                     mk<LEQ>(qVar, preconds[ind]->right());

          arrIterRanges[ind].insert(normalizeDisj(fla, invAndIterVarsAll));
          arrIterRanges[ind].insert(normalizeDisj(
                  replaceAll(postconds[ind], iterators[ind], qVar), invAndIterVarsAll));
        }

        auto nested = ruleManager.getNestedRel(invRel);
        if (nested != NULL)
        {
          int invNumTo = getVarIndex(nested->dstRelation, decls);
          // only one variable for now. TBD: find if we need more
          Expr qVar2 = bind::intConst(mkTerm<string> ("_FH_nst_it", m_efac));
          arrAccessVars[ind].push_back(qVar2);

          Expr range = conjoin (arrIterRanges[invNumTo], m_efac);
          ExprSet quantified;
          for (int i = 0; i < nested->dstVars.size(); i++)
          {
            range = replaceAll(range, invarVars[invNumTo][i], nested->dstVars[i]);
            quantified.insert(nested->dstVars[i]);
          }

          // naive propagation of ranges
          ExprSet cnjs;
          getConj(nested->body, cnjs);
          for (auto & a : cnjs)
          {
            for (auto & b : quantified)
            {
              if (isOpX<EQ>(a) && a->right() == b)
              {
                range = replaceAll(range, b, a->left());
              }
              else if (isOpX<EQ>(a) && a->left() == b)
              {
                range = replaceAll(range, b, a->right());
              }
            }
          }
          arrIterRanges[ind].insert(
                replaceAll(replaceAll(range, *arrAccessVars[invNumTo].begin(), qVar2),
                      iterators[ind], *arrAccessVars[ind].begin()));
        }

        // process all quantified seeds
        for (auto & a : tmpArrCands)
        {
          Expr replCand = a;
          for (int i = 0; i < 3; i++)
            for (auto & v : sf.lf.nonlinVars)
              replCand = replaceAll(replCand, v.second, v.first);
          if (!u.isEquiv(replCand, mk<TRUE>(m_efac)) && !u.isEquiv(replCand, mk<FALSE>(m_efac)))
          {
            ExprMap replLog;
            ExprSet tmpRanges;
            ExprSet concreteVals;
            if (prepareArrCand (replCand, replLog, arrAccessVars[ind], tmpRanges, concreteVals, ind) &&
               (contains(replCand, iterators[ind]) || !emptyIntersect(replCand, arrAccessVars[ind])))
            {
              // very cheeky heuristic: sometimes restrict, but sometimes extend the range
              // depending on existing constants
              if (u.isSat(conjoin(tmpRanges, m_efac), conjoin(arrIterRanges[ind], m_efac)))
              {
                arrIterRanges[ind].insert(tmpRanges.begin(), tmpRanges.end());
              }
              else
              {
                for (auto & a : tmpArrCands)
                  createGroundInstances (concreteVals, candsFromCode, a, iterators[ind]);
              }

              // at this point it should not happen, but sometimes it does. To debug.
              if (!findInvVar(ind, replCand, arrAccessVars[ind])) continue;

              for (auto iter : arrAccessVars[ind])
                arrCands[ind].insert(replaceAll(replCand, iterators[ind], iter));
            }
            else candsFromCode.insert(a);
          }
        }

        // trick for tiling benchs
        ExprSet afs;
        for (auto & a : tmpArrFuns)
        {
          ExprVector vars;
          filter (a, bind::IsConst(), std::inserter (vars, vars.begin ()));
          if (vars.size() != 1 || *vars.begin() == a) continue;
          afs.insert(replaceAll(a, *vars.begin(), arrAccessVars[ind][0]));
        }

        for (auto & qcand : arrCands[ind])
        {
          ExprSet se;
          filter (qcand, bind::IsSelect (), inserter(se, se.begin()));
          for (auto & arrsel : se)
            for (auto & s : afs)
            {
              Expr qcandTmp = replaceAll(qcand, arrsel->right(), s);
              arrCands[ind].insert(qcandTmp);
            }
        }
      }

      // process all quantifier-free seeds
      for (auto & cand : candsFromCode)
      {
        checked.clear();
        Expr replCand = cand;
        for (int i = 0; i < 3; i++)
          for (auto & v : sf.lf.nonlinVars)
            replCand = replaceAll(replCand, v.second, v.first);

        // sanity check for replCand:
        if (toCont (ind, replCand, arrAccessVars[ind]) && addCandidate(ind, replCand))
          propagate (ind, replCand, true);
      }
    }

    void refreshCands(map<Expr, ExprSet>& cands)
    {
      cands.clear();
      for (auto & a : candidates)
      {
        cands[decls[a.first]].insert(a.second.begin(), a.second.end());
      }
    }

    bool anyProgress(vector<HornRuleExt*> worklist)
    {
      for (int i = 0; i < invNumber; i++)
      {
        // simple check if there is a non-empty candidate
        for (auto & hr : worklist)
        {
          if (hr->srcRelation == decls[i] || hr->dstRelation == decls[i])
          {
            if (candidates[i].size() > 0)
            {
              return true;
            }
          }
        }
      }
      return false;
    }

#ifdef HAVE_ARMADILLO
    void getDataCandidates(map<Expr, ExprSet>& cands, const vector<string> & behaviorfiles){
      int fileIndex = 0;
      for (auto & dcl : decls) {
        DataLearner dl(ruleManager, m_z3);
        dl.initialize(dcl, true /*multipleLoops*/);
        string filename("");
        if (fileIndex < behaviorfiles.size()) {
          filename = behaviorfiles[fileIndex];
          fileIndex++;
        }
        if (!dl.computeData(filename)) continue;
        (void)dl.computePolynomials(cands[dcl]);
      }
    }
#endif

    bool bootstrap()
    {
      filterUnsat();

      if (multiHoudini(ruleManager.wtoCHCs))
      {
        assignPrioritiesForLearned();
        if (checkAllLemmas())
        {
          outs () << "Success after bootstrapping\n";
          return true;
        }
      }

      // try array candidates one-by-one (adapted from `synthesize`)
      // TODO: batching
      if (ruleManager.hasArrays)
      {
        for (auto & dcl: ruleManager.wtoDecls)
        {
          int i = getVarIndex(dcl, decls);
          SamplFactory& sf = sfs[i].back();
          for (auto & c : arrCands[i])
          {
            checked.clear();
            Expr cand = sf.af.getSimplCand(c);
//            outs () << " - - - bootstrapped cand for " << i << ": " << *cand << "\n";

            if (!addCandidate(i, cand)) continue;
            if (checkCand(i))
            {
              assignPrioritiesForLearned();
              generalizeArrInvars(sf);
              if (checkAllLemmas())
              {
                outs () << "Success after bootstrapping\n";
                return true;
              }
            }
          }
        }

        // second round of bootstrapping (to be removed after Houdini supports arrays)

        candidates.clear();
        ExprVector empt;
        for (auto &hr: ruleManager.chcs)
        {
          if (hr.isQuery)
          {
            int invNum = getVarIndex(hr.srcRelation, decls);
            ExprSet cnjs;
            getConj(hr.body, cnjs);
            for (auto & a : cnjs)
            {
              if (isOpX<NEG>(a) && findInvVar(invNum, a, empt))
              {
                candidates[invNum].push_back(a->left());
                break;
              }
            }
            break;
          }
        }
        if (multiHoudini(ruleManager.wtoCHCs))
        {
          assignPrioritiesForLearned();
          if (checkAllLemmas())
          {
            outs () << "Success after bootstrapping\n";
            return true;
          }
        }
      }

      return false;
    }

    void updateGrammars()
    {
      // convert candidates to curCandidates and run the method from RndLearner
      for (int ind = 0; ind < invNumber; ind++)
      {
        if (candidates[ind].size() == 0) curCandidates[ind] = mk<TRUE>(m_efac);
        else curCandidates[ind] = conjoin(candidates[ind], m_efac);
      }
      updateRels();
      updCount++;
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (int i = ruleManager.wtoCHCs.size() - 1; i >= 0; i--)
      {
        auto & hr = *ruleManager.wtoCHCs[i];
        if (!checkCHC(hr, candidates)) {
          if (!hr.isQuery)
            assert(0);    // only queries are allowed to fail
          else
            return false; // TODO: use this fact somehow
        }
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations)
    {
      ExprSet exprs;
      exprs.insert(hr.body);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        ExprSet lms = sf.learnedExprs;
        for (auto & a : annotations[ind]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.srcVars[v.first]);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        ExprSet lms = sf.learnedExprs;
        ExprSet negged;
        for (auto & a : annotations[ind]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[ind]) a = replaceAll(a, v.second, hr.dstVars[v.first]);
          negged.insert(mkNeg(a));
        }
        exprs.insert(disjoin(negged, m_efac));
      }
      return (bool)(!u.isSat(exprs));
    }

    void initArrayStuff(BndExpl& bnd, int cycleNum, Expr pref)
    {
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      int invNum = getVarIndex(ruleManager.chcs[cycle[0]].srcRelation, decls);
      if (iterators[invNum] != NULL) return;    // GF: TODO more sanity checks (if needed)

      ExprSet ssa;
      ssas[invNum] = bnd.toExpr(cycle);
      getConj(ssas[invNum], ssa);

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum], qvars[invNum].begin()));
      postconds[invNum] = ruleManager.getPrecondition(&ruleManager.chcs[cycle[0]]);

      for (int i = 0; i < bnd.bindVars.back().size(); i++)
      {
        Expr a = ruleManager.chcs[cycle[0]].srcVars[i];
        Expr b = bnd.bindVars.back()[i];
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        // TODO: pick one if there are multiple available
        if (u.implies(ssas[invNum], mk<GT>(a, b)))
        {
          iterators[invNum] = a;
          iterGrows[invNum] = false;
          break;
        }
        else if (u.implies(ssas[invNum], mk<LT>(a, b)))
        {
          iterators[invNum] = a;
          iterGrows[invNum] = true;
        }
      }

      ssa.clear();
      getConj(pref, ssa);
      for (auto & a : ssa)
      {
        if (contains(a, iterators[invNum]))
        {
          preconds[invNum] = a;
          break;
        }
      }
    }
  };

  inline void learnInvariants3(string smt, char * outfile, int maxAttempts, bool freqs, bool aggp, bool enableDataLearning, const vector<string> & behaviorfiles)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl bnd(ruleManager);

    if (!ruleManager.hasCycles())
    {
      bnd.exploreTraces(1, ruleManager.chcs.size(), true);
      return;
    }

    RndLearnerV3 ds(m_efac, z3, ruleManager, freqs, aggp);
    map<Expr, ExprSet> cands;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);

    if (enableDataLearning) {
#ifdef HAVE_ARMADILLO
      ds.getDataCandidates(cands, behaviorfiles);
#else
      outs() << "Skipping learning from data as required library (armadillo) not found\n";
#endif
    }

    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr pref = bnd.compactPrefix(i);
      cands[ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation].insert(pref);
      if (ruleManager.hasArrays) ds.initArrayStuff(bnd, i, pref);
    }

    for (auto& dcl: ruleManager.wtoDecls) ds.getSeeds(dcl, cands);
    ds.refreshCands(cands);
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)], false);
    ds.calculateStatistics();
    if (ds.bootstrap()) return;
    std::srand(std::time(0));
    ds.synthesize(maxAttempts, outfile);
  }
}

#endif
