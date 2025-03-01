#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>

#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;

namespace {
  bool isAllZeroes(std::string const& str) {
    return std::all_of(str.begin(), str.end(), [](char c){ return c == '0'; });
  }

  bool isAllOnes(std::string const& str) {
    return std::all_of(str.begin(), str.end(), [](char c){ return c == '1'; });
  }
}

namespace ufo
{
  inline static bool hasBoolSort(Expr e)
  {
    if (bind::isBoolConst(e) || isOp<BoolOp>(e)) return true;
    return false;
  }

  inline static bool isNumericConst(Expr e)
  {
    return isOpX<MPZ>(e) || isOpX<MPQ>(e);
  }

  static Expr mkNeg(Expr term);

  template<typename Range> static Expr conjoin(Range const& conjs, ExprFactory &efac){
    return
    (conjs.size() == 0) ? mk<TRUE>(efac) :
    (conjs.size() == 1) ? *conjs.begin() :
    mknary<AND>(conjs);
  }

  template<typename Range> static Expr disjoin(Range const & disjs, ExprFactory &efac){
    return
    (disjs.size() == 0) ? mk<FALSE>(efac) :
    (disjs.size() == 1) ? *disjs.begin() :
    mknary<OR>(disjs);
  }

  template<typename Range> static Expr mkplus(Range& terms, ExprFactory &efac){
    return
    (terms.size() == 0) ? mkTerm (mpz_class (0), efac) :
    (terms.size() == 1) ? *terms.begin() :
    mknary<PLUS>(terms);
  }

  template<typename Range> static Expr mkmult(Range& terms, ExprFactory &efac){
    return
    (terms.size() == 0) ? mkTerm (mpz_class (1), efac) :
    (terms.size() == 1) ? *terms.begin() :
    mknary<MULT>(terms);
  }

  template<typename Range1, typename Range2> static bool emptyIntersect(Range1& av, Range2& bv){
    for (auto &var1: av){
      for (auto &var2: bv) if (var1 == var2) return false;
    }
    return true;
  }

  template<typename Range> static bool emptyIntersect(Expr a, Range& bv){
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    return emptyIntersect(av, bv);
  }

  inline static bool emptyIntersect(Expr a, Expr b){
    ExprVector bv;
    filter (b, bind::IsConst (), inserter(bv, bv.begin()));
    return emptyIntersect(a, bv);
  }

  // if at the end disjs is empty, then a == true
  inline static void getConj (Expr a, ExprSet &conjs)
  {
    if (isOpX<TRUE>(a)) return;
    if (isOpX<FALSE>(a)){
      conjs.clear();
      conjs.insert(a);
      return;
    } else if (isOpX<AND>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getConj(a->arg(i), conjs);
      }
    } else {
      conjs.insert(a);
    }
  }

  // if at the end disjs is empty, then a == false
  inline static void getDisj (Expr a, ExprSet &disjs)
  {
    if (isOpX<FALSE>(a)) return;
    if (isOpX<TRUE>(a)){
      disjs.clear();
      disjs.insert(a);
      return;
    } else if (isOpX<OR>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getDisj(a->arg(i), disjs);
      }
    } else {
      disjs.insert(a);
    }
  }

  inline static void getCounters (Expr a, ExprVector &cntrs)
  {
    if (isOpX<SELECT>(a) || isOpX<STORE>(a)){
      cntrs.push_back(a->right());
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getCounters(a->arg(i), cntrs);
    }
  }

  inline static void getArrIneqs (Expr a, ExprSet &ineqs)
  {
    if (isOp<ComparissonOp>(a) && containsOp<SELECT>(a)){
      if (isOpX<EQ>(a))
      {
        ineqs.insert(mk<LEQ>(a->left(), a->right()));
        ineqs.insert(mk<GEQ>(a->left(), a->right()));
      }
      else
      {
        ineqs.insert(a);
      }
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getArrIneqs(a->arg(i), ineqs);
    }
  }

  inline static void getMultOps (Expr a, ExprVector &ops)
  {
    if (isOpX<MULT>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getMultOps(a->arg(i), ops);
      }
    } else {
      ops.push_back(a);
    }
  }

  /**
   * Represent Expr as multiplication
   */
  inline static Expr mult(Expr e){
    if (isOpX<MULT>(e)){
      return e;
    } else {
      return mk<MULT>(mkTerm (mpz_class (1), e->getFactory()), e);
    }
  }
  
  /**
   * Represent Zero as multiplication
   */
  inline static Expr multZero(Expr e, Expr multiplier){
    if (lexical_cast<string>(e) == "0")
      return mk<MULT>(multiplier, e);
    else return e;
  }
  
  /**
   * Rewrites distributivity rule:
   * a*b + a*c -> a*(b + c)
   * (assume, all common multipliers might be only in the first place)
   */
  inline static Expr exprDistributor(Expr e){
    if (e->arity () == 0) return e;
    Expr multiplier = mult(e->arg(0));
    ExprSet newE;
    newE.insert(multiplier->right());
    multiplier = multiplier->left();
    
    for (unsigned i = 1; i < e->arity (); i++){
      Expr a = mult(e->arg(i));
      if (isOpX<MULT>(a)){
        if (a->left() == multiplier){
          newE.insert(a->right());
        } else {
          return e;
        }
      } else {
        return e;
      }
    }
    if (isOpX<PLUS>(e)){
      return mk<MULT>(multiplier, mknary<PLUS>(newE));
    }
    return e;
  }
  
  /**
   * Self explanatory
   */
  inline static bool isConstOrItsAdditiveInverse(Expr e, Expr var){
    if (e == var) {
      return true;
    }
    if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1" && e->right() == var){
        return true;
      }
    }
    
    return false;
  }
  
  /**
   * Self explanatory
   */
  inline static Expr additiveInverse(Expr e){
    if (isOpX<UN_MINUS>(e)){
      return e->left();
    }
    else if (isOpX<MPQ>(e)){
      string val = lexical_cast<string>(e);
      int delim = val.find("/");
      int val1 = stoi(val.substr(0, delim));
      int val2 = stoi(val.substr(delim + 1));
      if (delim < 0) {
        return mkTerm (mpq_class (-val1), e->getFactory());
      } else {
        string inv_val = to_string(-val1) + "/" + to_string(val2);
        return mkTerm (mpq_class (inv_val), e->getFactory());
      }
    }
    else if (isOpX<MPZ>(e)){
      int val = lexical_cast<int>(e);
      return mkTerm (mpz_class (-val), e->getFactory());
    }
    else if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1"){
        return e->right();
      } else if (e->arity() == 2) {
        Expr c = additiveInverse(e->left());
        return mk<MULT>(c, e->right());
      }
    }
    else if (bind::isIntConst(e))
      return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);

    // otherwise could be buggy...
    return mk<MULT>(mkTerm (mpq_class (-1), e->getFactory()), e);
  }
  
  /**
   * Commutativity in Addition
   */
  inline static Expr exprSorted(Expr e){
    Expr res = e;
    if (isOpX<PLUS>(e)) {
      ExprSet expClauses;
      for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it){
        expClauses.insert(*it);
      }
      res = mknary<PLUS>(expClauses);
    }
    
    if (isOpX<MULT>(e)) {
      if (lexical_cast<string>(e->left())  == "-1"){
        Expr l = e->right();
        
        if (isOpX<PLUS>(l)) {
          ExprSet expClauses;
          for (auto it = l->args_begin(), end = l->args_end(); it != end; ++it){
            expClauses.insert(additiveInverse(*it));
          }
          res = mknary<PLUS>(expClauses);
        }
      }
    }
    
    return res;
  }
  
  /**
   * Helper used in ineqReverter
   */
  template <typename T> static Expr rewriteHelperN(Expr e){
    assert(e->arity() == 2);
    
    if (!isOpX<UN_MINUS>(e->left()) &&
        !(isOpX<MULT>(e->left())))
    {
      if (lexical_cast<string>(e->left()->left()) == "-1")  return e;
    }

    return mk<T>(additiveInverse(e->left()), additiveInverse(exprDistributor(e->right())));
  }
  
  /**
   *  Helper used in ineqMover
   */
  template <typename T> static Expr rewriteHelperM(Expr e, Expr var){
    Expr l = e->left();
    Expr r = e->right();
    ExprVector lhs;  // expressions containing var
    ExprVector rhs;  // the rest of e
    
    // first, parse l;
    
    if (isOpX<PLUS>(l)){
      for (unsigned i = 0; i < l->arity (); i++){
        Expr a = l->arg(i);
        if (isConstOrItsAdditiveInverse(a, var)){
          lhs.push_back(a);
        } else {
          rhs.push_back(additiveInverse(a));
        }
      }
    } else if (isOpX<MINUS>(l)){
      if (isConstOrItsAdditiveInverse(l->left(), var)){
        lhs.push_back(l->left());
      } else {
        rhs.push_back(additiveInverse(l->left()));
      }
      if (isConstOrItsAdditiveInverse(l->right(), var)){
        lhs.push_back(additiveInverse(l->right()));
      } else {
        rhs.push_back(l);
      }
    } else {
      if (isConstOrItsAdditiveInverse(l, var)){
        lhs.push_back(l);
      } else if (lexical_cast<string>(l) != "0"){
        rhs.push_back(additiveInverse(l));
      }
    }
    
    // second, parse r;
    
    if (isOpX<PLUS>(r)){
      for (unsigned i = 0; i < r->arity (); i++){
        Expr a = r->arg(i);
        if (isConstOrItsAdditiveInverse(a, var)){
          lhs.push_back(additiveInverse(a));
        } else {
          rhs.push_back(a);
        }
      }
    } else if (isOpX<MINUS>(r)){
      if (isConstOrItsAdditiveInverse(r->left(), var)){
        lhs.push_back(additiveInverse(r->left()));
      } else {
        rhs.push_back(r->left());
      }
      if (isConstOrItsAdditiveInverse(r->right(), var)){
        lhs.push_back(r->right());
      } else {
        rhs.push_back(r->right());
      }
    } else {
      if (isConstOrItsAdditiveInverse(r, var)){
        lhs.push_back(additiveInverse(r));
      } else if (lexical_cast<string>(r) != "0"){
        rhs.push_back(r);
      }
    }
    
    // third, combine results;
    
    int coef = 0;
    for (auto &a : lhs)
    {
      if (a == var) coef++;
      if (var == additiveInverse(a)) coef--;
    }

    r = mkplus(rhs, e->getFactory());

    if (coef == 0){
      l = mkTerm (mpz_class (0), e->getFactory());
    } else if (coef == 1){
      l = var;
    } else {
      l = mk<MULT>(mkTerm (mpz_class (coef), e->getFactory()), var);
    }

    return mk<T>(l,r);
  }
  
  /**
   * Helper used in exprMover
   */
  template <typename T> static Expr rewriteHelperE(Expr e, Expr var){
    //todo: debug: clean = false -> shared_ptr.hpp:418: Assertion `px != 0' failed
    assert(e->arity() == 2);
    Expr l = e->left();
    Expr r = e->right();
    if (r == var) {
      l = exprSorted(l);
      return mk<T>(r, l);
    }
    
    if (isOpX<MULT>(r)){
      if (r->left() == var || r->right() == var){
        l = exprSorted(l);
        return mk<T>(r, l);
      }
    }
    return e;
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= b && a >= b) -> (a == b)
   */
  inline static void ineqMerger(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<LEQ>(e)){
        for (auto &e2: expClauses){
          if (isOpX<GEQ>(e2)){
            if (e->left() == e2->left()){
              Expr e1r = exprSorted(e->right());
              Expr e2r = exprSorted(e2->right());
              if ( e1r == e2r ){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e1r));
              }
            }
          }
        }
      }
    }
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= b && b <= a) -> (a == b)
   */
  template <typename T> static void ineqMergerSwap(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->left() == e2->right() && e->right() == e2->left()){
              if (clean){
                expClauses.erase(e);
                expClauses.erase(e2);
              }
              expClauses.insert(mk<EQ>(e->left(), e->right()));
            }
          }
        }
      }
    }
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= 0 && -a <= 0) -> (a == 0)
   *  (a >= 0 && -a >= 0) -> (a == 0)
   */
  template <typename T> static void ineqMergerSwapMinus(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->right() == e2->right() && e2->right() == mkTerm (mpz_class (0), e2->getFactory())){
              Expr l1 = exprSorted(additiveInverse(e->left()));
              Expr l2 = exprSorted(e2->left());
              if (l1 == l2){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e->right()));
              }
            }
          }
        }
      }
    }
  }
  
  /**
   *  Trivial simplifier:
   *  (-1*a <= -1*b) -> (a >= b)
   *  (-1*a >= -1*b) -> (a <= b)
   *  (-1*a == -1*b) -> (a == b)
   */
  inline static Expr ineqReverter(Expr e){
      if (isOpX<LEQ>(e)){
        return rewriteHelperN<GEQ>(e);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperN<LEQ>(e);
      } else if (isOpX<LT>(e)){
        return rewriteHelperN<GT>(e);
      } else if (isOpX<GT>(e)){
        return rewriteHelperN<LT>(e);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperN<EQ>(e);
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperN<NEQ>(e);
      }
    return e;
  }
  
  inline static Expr ineqNegReverter(Expr a){
    if (isOpX<NEG>(a)){
      Expr e = a->arg(0);
      if (isOpX<LEQ>(e)){
        return mk<GT>(e->arg(0), e->arg(1));
      } else if (isOpX<GEQ>(e)){
        return mk<LT>(e->arg(0), e->arg(1));
      } else if (isOpX<LT>(e)){
        return mk<GEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<GT>(e)){
        return mk<LEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<NEQ>(e)){
        return mk<EQ>(e->arg(0), e->arg(1));
      } else if (isOpX<EQ>(e)){
        return mk<NEQ>(e->arg(0), e->arg(1));
      }
    }
    return a;
  }
  
  /**
   *  Transform the inequalities by the following rules:
   *  (a + .. + var + .. + b <= c ) -> (var <= -1*a + .. + -1*b + c)
   *  (a + .. + -1*var + .. + b <= c) -> (-1*var <= -1*a + .. + -1*b + c )
   *  (a <= b + .. + var + .. + c) -> (-1*var <= (-1)*a + b + .. + c)
   *  (a <= b + .. + (-1)*var + .. + c) -> (var <= (-1)*a + b + .. + c)
   *
   *  same for >=
   */
  inline static Expr ineqMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperM<LEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperM<GEQ>(e, var);
      } else if (isOpX<LT>(e)){
        return rewriteHelperM<LT>(e, var);
      } else if (isOpX<GT>(e)){
        return rewriteHelperM<GT>(e, var);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperM<EQ>(e, var);
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperM<NEQ>(e, var);
      }
    return e;
  }
  
  /**
   *  Move "var" to the left hand side of expression:
   *  (a <= var) -> (var >= b)
   *  (a >= var) -> (var <= b)
   *  (a == var) -> (var == b)
   */
  inline static Expr exprMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperE<GEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperE<LEQ>(e, var);
      } if (isOpX<EQ>(e)){
        return rewriteHelperE<EQ>(e, var);
      } if (isOpX<NEG>(e)){
        return mk<NEG>(exprMover(e->arg(0), var));
      }
    return e;
  }
  
  /**
   *
   */
  inline static Expr eqDiffMover(Expr e){
    if(isOpX<EQ>(e)){
      if (isOpX<MINUS>(e->left()) && e->left()->arity() == 2 && lexical_cast<string>(e->right()) == "0"){
        return mk<EQ>(e->left()->left(), e->left()->right());
      }
    }
    return e;
  }
  
  /**
   * Search for an equality
   */
  inline static bool equalitySearch(ExprSet& expClauses, Expr var){
    for (auto &e: expClauses){
      if (isOpX<EQ>(e)){
        Expr l = e->left();
        Expr r = e->right();
        if (l == var || r == var){
          ExprSet singleton;
          singleton.insert(e);
          expClauses = singleton;
          return true;
        }
      }
    }
    return false;
  }
  
  /**
   * Simplifier Wrapper
   */
  inline static Expr ineqSimplifier(Expr v, Expr exp){
    ExprSet substsMap;
    if (isOpX<AND>(exp)){
      for (ENode::args_iterator it = exp->args_begin(), end = exp->args_end();
           it != end; ++it){
        Expr cl = *it;
        cl = exprMover(*it, v);
        cl = ineqMover(cl, v);
        cl = ineqReverter (cl);
        substsMap.insert(cl);
      }
      
      ineqMerger(substsMap);
      equalitySearch(substsMap, v);
      return conjoin(substsMap, v->getFactory());
      
    }
    return exp;
  }

  template<typename T> static void unique_push_back(T e, vector<T>& v) {
    if (find(v.begin(), v.end(), e) == v.end()) v.push_back(e);
  }

  template<typename T>
  struct RW
  {
    std::shared_ptr<T> _r;
    
    RW (std::shared_ptr<T> r) : _r(r) {}
    RW (T *r) : _r (r) {}
    
    
    VisitAction operator() (Expr exp)
    {
      // -- apply the rewriter
      if (exp->arity() == 0)
        // -- do not descend into non-boolean operators
        return VisitAction::skipKids ();
      
      return VisitAction::changeDoKidsRewrite (exp, _r);
      
    }
  };

  inline static int separateConst(ExprVector& plsOps)
  {
    int c = 0;
    for (auto it = plsOps.begin(); it != plsOps.end(); )
    {
      if (isOpX<MPZ>(*it))
      {
        c += lexical_cast<int>(*it);
        it = plsOps.erase(it);
        continue;
      }
      else ++it;
    }
    return c;
  }

  inline static void getPlusTerms (Expr a, ExprVector &terms)
  {
    if (isOpX<PLUS>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getPlusTerms(a->arg(i), terms);
      }
    }
    else if (isOpX<MINUS>(a)){
      // assume only two args
      terms.push_back(a->left());
      terms.push_back(additiveInverse(a->right()));
    } else {
      terms.push_back(a);
    }
  }

  inline static Expr simplifyPlus (Expr exp){
    ExprVector plsOps;
    getPlusTerms (exp, plsOps);
    // GF: to extend
    int c = separateConst(plsOps);
    if (c != 0) plsOps.push_back(mkTerm (mpz_class (c), exp->getFactory()));
    return mkplus(plsOps, exp->getFactory());
  }

  static Expr reBuildCmp(Expr term, Expr lhs, Expr rhs);

  inline static Expr simplifyCmp (Expr exp)
  {
    ExprFactory &efac = exp->getFactory();

    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getPlusTerms(exp->left(), plusOpsLeft);
    getPlusTerms(exp->right(), plusOpsRight);

    int c1 = separateConst(plusOpsLeft);
    int c2 = separateConst(plusOpsRight);

    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      bool found = false;
      for (auto it2 = plusOpsRight.begin(); it2 != plusOpsRight.end(); )
      {
        if (*it1 == *it2)
        {
          found = true;
          plusOpsRight.erase(it2);
          break;
        }
        else
        {
          ++it2;
        }
      }
      if (found) it1 = plusOpsLeft.erase(it1);
      else ++it1;
    }

    if (c1 > c2)
      plusOpsLeft.push_back(mkTerm (mpz_class (c1 - c2), efac));
    else if (c1 < c2)
      plusOpsRight.push_back(mkTerm (mpz_class (c2 - c1), efac));

    return reBuildCmp(exp, mkplus(plusOpsLeft, efac), mkplus(plusOpsRight, efac));
  }

  // GF: to rewrite/remove
  inline static Expr simplifiedPlus (Expr exp, Expr to_skip){
    ExprVector args;
    Expr ret;
    bool f = false;
    
    for (ENode::args_iterator it = exp->args_begin(),
         end = exp->args_end(); it != end; ++it){
      if (*it == to_skip) f = true;
      else args.push_back (*it);
    }

    if (f == false)
    {
      args.push_back(additiveInverse(to_skip));
    }
    
    if (args.size() == 1) {
      ret = args[0];
    }
    
    else if (args.size() == 2){
      if (isOpX<UN_MINUS>(args[0]) && !isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[1], args[0]->left());
      else if (!isOpX<UN_MINUS>(args[0]) && isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[0], args[1]->left());
      
      else ret = mknary<PLUS>(args);
      
    } else {
      ret = mknary<PLUS>(args);
    }
    return ret;
  }
  
  // return a - b
  inline static Expr simplifiedMinus (Expr a, Expr b){
    Expr ret = mk<MINUS>(a, b);
    
    if (a == b) {
      ret = mkTerm (mpz_class (0), a->getFactory());
    } else
      
      if (isOpX<PLUS>(a)){
        return simplifiedPlus(a, b);
      } else
        
        if (isOpX<PLUS>(b)){
          Expr res = simplifiedPlus(b, a);
          return mk<UN_MINUS>(res);
        } else
          
          if (isOpX<MINUS>(a)){
            if (a->left() == b) ret = mk<UN_MINUS>(a->right());
          } else
            
            if (isOpX<MINUS>(b)){
              if (a == b->right()) ret = mk<UN_MINUS>(b->left());
            } else
              
              if (isOpX<UN_MINUS>(b)) {
                if (b->left() == mkTerm (mpz_class (0), a->getFactory())) {
                  ret = a;
                } else {
                  ret = mk<PLUS>(a,b->left());
                }
              } else
                
                if (mkTerm (mpz_class (-1), a->getFactory()) == b) {
                  ret = simplifiedPlus(a, mkTerm (mpz_class (1), a->getFactory()));
                } else
                  
                  if (b == mkTerm (mpz_class (0), a->getFactory())) {
                    ret = a;
                  } else
                    
                    if (a == mkTerm (mpz_class (0), a->getFactory())){
                      if (isOpX<UN_MINUS>(b)){
                        ret = b->left();
                      }
                      else {
                        ret = mk<UN_MINUS>(b);
                      }
                    }
    
    return ret;
  }

  inline static bool isNumeric(Expr a)
  {
    // don't consider ITE-s
    return (isOp<NumericOp>(a) || isOpX<MPZ>(a) ||
            isOpX<MPQ>(a) || bind::isIntConst(a) || isOpX<SELECT>(a)
            || bv::is_bvnum(a));
  }

  struct SimplifyArithmExpr
  {
    ExprFactory &efac;
    
    Expr zero;
    Expr one;
    Expr minus_one;

    SimplifyArithmExpr (ExprFactory& _efac):
    efac(_efac)
    {
      zero = mkTerm (mpz_class (0), efac);
      one = mkTerm (mpz_class (1), efac);
      minus_one = mkTerm (mpz_class (-1), efac);
    };

    Expr operator() (Expr exp)
    {
      if (isOpX<PLUS>(exp))
      {
        return simplifyPlus(exp);
      }

      if (isOpX<MINUS>(exp) && exp->arity() == 2)
      {
        return simplifiedMinus(exp->left(), exp->right());
      }

      if (isOpX<MULT>(exp))
      {
        if (exp->left() == zero) return zero;
        if (exp->right() == zero) return zero;
        if (exp->left() == one) return exp->right();
        if (exp->right() == one) return exp->left();
        if (exp->left() == minus_one) return additiveInverse(exp->right());
        if (exp->right() == minus_one) return additiveInverse(exp->left());
      }

      if (isOpX<UN_MINUS>(exp))
      {
        Expr uneg = exp->left();
        if (uneg == zero) return zero;
        if (uneg == minus_one) return one;
        if (isOpX<UN_MINUS>(uneg)) return uneg->left();
        if (isOpX<PLUS>(uneg)){
          Expr unegl = uneg->left();
          Expr unegr = uneg->right();
          if (isOpX<UN_MINUS>(unegl)) return mk<MINUS>(unegl->left(), unegr);
          if (isOpX<UN_MINUS>(unegr)) return mk<MINUS>(unegr->left(), unegl);
        }
      }

      if (isOpX<MINUS>(exp))
      {
        if (isOpX<UN_MINUS>(exp->right())) return mk<PLUS>(exp->left(), exp->right()->left());
      }

      if (isOp<ComparissonOp>(exp) && isNumeric(exp->right()))
      {
        return simplifyCmp(exp);
      }
      return exp;
    }
  };

  inline static Expr simplifyBool (Expr exp);

  struct SimplifyBoolExpr
  {
    ExprFactory &efac;
    
    SimplifyBoolExpr (ExprFactory& _efac) : efac(_efac){};
    
    Expr operator() (Expr exp)
    {
      // GF: to enhance

      if (isOpX<IMPL>(exp))
      {
        if (isOpX<TRUE>(exp->right()))
          return mk<TRUE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return mk<NEG>(exp->left());
        
        return (mk<OR>(
                 mk<NEG>(exp->left()),
                 exp->right()));
      }

      if (isOpX<EQ>(exp))
      {
        if (isOpX<TRUE>(exp->right()))
          return exp->left();

        if (isOpX<TRUE>(exp->left()))
          return exp->right();

        if (isOpX<FALSE>(exp->right()))
          return mk<NEG>(exp->left());

        if (isOpX<FALSE>(exp->left()))
          return mk<NEG>(exp->right());
      }

      if (isOpX<OR>(exp))
      {
        ExprSet dsjs;
        ExprSet newDsjs;
        getDisj(exp, dsjs);
        for (auto & a : dsjs){
          if (isOpX<TRUE>(a))
          {
            return mk<TRUE>(efac);
          }
          if (isOpX<FALSE>(a))
          {
            continue;
          }
          newDsjs.insert(simplifyBool(a));
        }
        return disjoin (newDsjs, efac);
      }

      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(exp, cnjs);
        for (auto & a : cnjs){
          if (isOpX<FALSE>(a))
          {
            return mk<FALSE>(efac);
          }
          if (isOpX<TRUE>(a))
          {
            continue;
          }
          newCnjs.insert(simplifyBool(a));
        }
        return conjoin (newCnjs, efac);
      }

      if (isOpX<ITE>(exp)) {
        Expr cond = simplifyBool(exp->arg(0));
        Expr br1 = hasBoolSort(exp->arg(1)) ? simplifyBool(exp->arg(1)) : exp->arg(1);
        Expr br2 = hasBoolSort(exp->arg(2)) ? simplifyBool(exp->arg(2)) : exp->arg(2);
        if (isOpX<TRUE>(cond)) return br1;
        if (isOpX<FALSE>(cond)) return br2;

        if (br1 == br2) return br1;

        if (isOpX<TRUE>(br1) && isOpX<FALSE>(br2)) return cond;

        if (isOpX<FALSE>(br1) && isOpX<TRUE>(br2)) return mkNeg(cond);
        return mk<ITE>(cond, br1, br2);
      }

      return exp;
    }
  };

  static inline Expr concatConstants(Expr f, Expr s) {
    assert(bv::is_bvnum(f));
    assert(bv::is_bvnum(s));
    std::string f_str = bv::constToBinary(f);
    std::string s_str = bv::constToBinary(s);
    assert(bv::width(f->right()) == f_str.size());
    assert(bv::width(s->right()) == s_str.size());
    std::string res_str = f_str + s_str;
    Expr res = bv::constFromBinary(res_str, res_str.size(), f->getFactory());
    return res;
  }
  template<typename Range>
  static inline Expr concatConstants(const Range& r) {
    std::vector<std::string> strs;
    std::transform(std::begin(r), std::end(r), std::back_inserter(strs),
        [](Expr e) {return bv::constToBinary(e); });
    std::string res_str = "";
    for (auto const& s : strs) { res_str.append(s); }
    assert(!res_str.empty());
    Expr res = bv::constFromBinary(res_str, res_str.size(), (*std::begin(r))->getFactory());
    return res;
  }

  struct SimplifyBVExpr
  {
    ExprFactory &efac;
    std::map<Expr, unsigned>& bitwidths;

    Expr zero;
    Expr one;

    SimplifyBVExpr (ExprFactory& _efac, std::map<Expr, unsigned>& bitwidths)
      : efac(_efac), bitwidths(bitwidths)
    {
      zero = mkTerm (mpz_class (0), efac);
      one = mkTerm (mpz_class(1), efac);
    };

    // This is intended to use with RW visitor, so it assumes the kids have been processed already
    Expr operator() (Expr exp)
    {
//      std::cout << exp << std::endl;
      getBitWidth(exp);
      if (isOpX<BEXTRACT>(exp)) {
        if (bv::high(exp) == 0 && bv::low(exp)== 0)
        {
          Expr extractArg = exp->arg(2);
          auto it = bitwidths.find(extractArg);
          if (it != bitwidths.end() && it->second == 1) {
            return extractArg;
          }
        }
      }
      if (isOpX<ITE>(exp))
      {
        Expr cond = exp->arg(0);
        Expr br1 =  exp->arg(1);
        Expr br2 =  exp->arg(2);
        if (isOpX<TRUE>(cond)) return br1;
        if (isOpX<FALSE>(cond)) return br2;
        if (br1 == br2) return br1;
        auto it = bitwidths.find(exp);
        if (it != bitwidths.end() && it->second == 1) {
          if (isOneBV(br1) && isZeroBV(br2)) {
            Expr ret = bv::frombool(cond);
            bitwidths[ret] = 1;
            return ret;
          }

          if (isZeroBV(br1)) {
            Expr ret = nullptr;
            if (isOneBV(br2)) {
              ret = bv::frombool(mkNeg(cond));
            }
            else {
              ret = bv::frombool(mk<AND>(mkNeg(cond), bv::tobool(br2)));
            }
            bitwidths[ret] = 1;
            return ret;
          }
          if (isZeroBV(br2)) {
            Expr ret = nullptr;
            if (isOneBV(br1)) {
              ret = bv::frombool(cond);
            }
            else {
              ret = bv::frombool(mk<AND>(cond, bv::tobool(br1)));
            }
            bitwidths[ret] = 1;
            return ret;
          }
          Expr br1_new = bv::tobool(br1);
          Expr br2_new = bv::tobool(br2);
          Expr ret = bv::frombool(mk<ITE>(cond, br1_new, br2_new));
          bitwidths[ret] = 1;
          return ret;
        }
      }
      if (isOpX<BNOT>(exp))
      {
        Expr arg = exp->first();
        if (isOpX<BOOL2BV>(arg)) {
          Expr ret = bv::frombool(mkNeg(arg->first()));
          bitwidths[ret] = 1;
          return ret;
        }
//        std::cerr << exp << std::endl;
        auto it = bitwidths.find(arg);
        if (it != bitwidths.end() && it->second == 1) {
          Expr ret = bv::frombool(mkNeg(bv::tobool(arg)));
          bitwidths[ret] = 1;
          return ret;
        }
        return exp;
      }
      if (isOpX<EQ>(exp) || isOpX<NEQ>(exp)) {
        Expr left = exp->left();
        Expr right = exp->right();
        auto it = bitwidths.find(left);
        if (it != bitwidths.end() && it->second == 1) {
          assert(bitwidths.find(right) != bitwidths.end() && bitwidths.find(right)->second == 1);
          const bool isLeftConstant = bv::is_bvnum(left);
          const bool isRightConstant = bv::is_bvnum(right);
          if (isLeftConstant || isRightConstant) {
            Expr constant = isLeftConstant ? left : right;
            Expr other = isLeftConstant ? right : left;
            bool negative = (isOpX<EQ>(exp) ^ isOneBV(constant));
            Expr res = negative ? mkNeg(bv::tobool(other)) : bv::tobool(other);
            return res;
          }
        }
      }
      if (isOpX<BOR>(exp) && exp->arity() == 2)
      {
        auto it = bitwidths.find(exp);
        if (it != bitwidths.end() && it->second == 1)
        {
          Expr left = exp->left();
          Expr right = exp->right();
          assert(bitwidths.find(left) != bitwidths.end() && bitwidths.find(left)->second == 1);
          assert(bitwidths.find(right) != bitwidths.end() && bitwidths.find(right)->second == 1);
          Expr res = bv::frombool(disjoin(ExprVector{bv::tobool(left), bv::tobool(right)}, efac));
          bitwidths[res] = 1;
          return res;
        }
        Expr left = exp->left();
        Expr right = exp->right();
        if (bv::is_bvnum(left) || bv::is_bvnum(right)) {
          Expr constant = bv::is_bvnum(left) ? left : right;
          Expr other = constant == left ? right : left;
          if (isOpX<BCONCAT>(other)) {
            Expr first = other->first();
            Expr second = other->arg(1);
            auto it1 = bitwidths.find(first);
            auto it2 = bitwidths.find(second);
            assert(it1 != bitwidths.end() && it2 != bitwidths.end());
            int width1 = it1->second;
            int width2 = it2->second;
            // For now let's simplify only when the two parts of constant are either 0 or all 1s
            auto it_const = bitwidths.find(constant);
            assert( it_const != bitwidths.end() && it_const->second == width1 + width2);
            int width = width1 + width2;
            auto const_str = bv::constToBinary(constant);
            auto str1 = const_str.substr(0, width1);
            auto str2 = const_str.substr(width1, width2);
            if ((isAllZeroes(str1) || isAllOnes(str1)) && (isAllZeroes(str2) || isAllOnes(str2))) {
              Expr arg1_new = isAllZeroes(str1) ? first : bv::constFromBinary(str1, width1, exp->getFactory());
              Expr arg2_new = isAllZeroes(str2) ? second : bv::constFromBinary(str2, width2, exp->getFactory());
              Expr res = mk<BCONCAT>(arg1_new, arg2_new);
//              std::cout << *res << std::endl;
              bitwidths[res] = width;
              return res;
            }
          }
        }
      }
      if (isOpX<BCONCAT>(exp)) {
        Expr first = exp->first();
        Expr second = exp->arg(1);
        const bool isFirstConstant = bv::is_bvnum(first);
        const bool isSecondConstant = bv::is_bvnum(second);
        if ( isFirstConstant || isSecondConstant ) {
          if (isFirstConstant && isSecondConstant) {
            Expr res = concatConstants(first, second);
            bitwidths[res] = bitwidths.at(first) + bitwidths.at(second);
            return res;
          }
          Expr constant = bv::is_bvnum(first) ? first : second;
          Expr other = bv::is_bvnum(first) ? second : first;
          if (isOpX<ITE>(other)) {
            // FOR now simplify only if ite returns constant
            bool returnsConstant = bv::is_bvnum(other->arg(1)) && bv::is_bvnum(other->arg(2));
            if (returnsConstant) {
              // propagate concatenation of constant inside ite
              Expr n_then = isFirstConstant ? concatConstants(constant, other->arg(1)) : concatConstants(other->arg(1), constant);
              Expr n_else = isFirstConstant ? concatConstants(constant, other->arg(2)) : concatConstants(other->arg(2), constant);
              Expr res = mk<ITE>(other->first(), n_then, n_else);
              bitwidths[res] = bitwidths.at(other) + bitwidths.at(constant);
              return res;
            }
          }
          if (isOpX<BOOL2BV>(other)) {
            Expr bvone = bv::bvnum(one, bv::bvsort(1, one->getFactory()));
            Expr bvzero = bv::bvnum(zero, bv::bvsort(1, zero->getFactory()));
            Expr n_then = isFirstConstant ? concatConstants(constant, bvone) : concatConstants(bvone, constant);
            Expr n_else = isFirstConstant ? concatConstants(constant, bvzero) : concatConstants(bvzero, constant);
            Expr res = mk<ITE>(other->first(), n_then, n_else);
            assert(bitwidths.at(other) == 1);
            bitwidths[res] = bitwidths.at(other) + bitwidths.at(constant);
            return res;
          }
        }
      }
      if (isOpX<AND>(exp)) {
        auto bwit = bitwidths.find(exp);
        if (bwit != bitwidths.end() && bwit->second == 1 && exp->arity() == 2)
        {
          Expr left = exp->left();
          Expr right = exp->right();
          assert(bitwidths.find(left) != bitwidths.end() && bitwidths.find(left)->second == 1);
          assert(bitwidths.find(right) != bitwidths.end() && bitwidths.find(right)->second == 1);
          Expr res = bv::frombool(conjoin(ExprVector{bv::tobool(left), bv::tobool(right)}, efac));
          bitwidths[res] = 1;
          return res;
        }
        ExprSet conjuncts;
        getConj(exp, conjuncts);
        ExprVector conjVec(conjuncts.begin(), conjuncts.end());
        auto beg = std::begin(conjVec);
        auto end = std::end(conjVec);
        auto boundary = std::partition(beg, end, [](Expr e) {
          if (!isOpX<EQ>(e)) return false;
          Expr lhs = e->left();
          Expr rhs = e->right();
          const bool isLeftExtract = isOpX<BEXTRACT>(lhs);
          const bool isRightExtract = isOpX<BEXTRACT>(rhs);
          if (!isLeftExtract && !isRightExtract) { return false; }
          const bool isLeftConst = bv::is_bvnum(lhs);
          const bool isRightConst = bv::is_bvnum(rhs);
          if (!isLeftConst && !isRightConst) { return false; }
          return true;
        });
        if (std::distance(beg, boundary) > 1) {
          // There is hope to join extracts only if there is more than one
          std::map<Expr, std::vector<std::pair<Expr, Expr>>> varToExtracts;
          for (auto it = beg; it != boundary; ++it) {
            Expr conjunct = *it;
            const bool isLeftExtract = isOpX<BEXTRACT>(conjunct->left());
            Expr extract = isLeftExtract ? conjunct->left() : conjunct->right();
            Expr constant = isLeftExtract ? conjunct->right() : conjunct->left();
            Expr extr_arg = extract->arg(2);
            varToExtracts[extr_arg].emplace_back(extract, constant);
          }
          ExprVector res;
          for (auto& entry : varToExtracts) {
            if (entry.second.size() > 1) {
              // we can hope to simplify it here
              auto& args = entry.second;
              std::sort(args.begin(), args.end(),
                  [](std::pair<Expr,Expr> const& p1, std::pair<Expr,Expr> const& p2)
                  {
                    return bv::high(p2.first) < bv::high(p1.first);
                  });
              const bool isConsecutive = [](std::vector<std::pair<Expr, Expr>> const& v) {
                  for (int i = 0; i < v.size() - 1; ++i) {
                    if (bv::high(v[i+1].first) != bv::low(v[i].first) - 1) { return false; }
                  }
                  return true;
                }(args);
              if (isConsecutive) {
                Expr n_lhs = bv::extract(bv::high(args[0].first), bv::low(args.back().first), entry.first);
                if (bv::low(n_lhs) == 0 && bv::high(n_lhs) == bitwidths[entry.first] - 1) {
                  n_lhs = entry.first;
                }
                ExprVector constants;
                std::transform(args.begin(), args.end(), std::back_inserter(constants),
                    [](std::pair<Expr, Expr> const& p){ return p.second; });
                Expr n_rhs = concatConstants(constants);
                res.push_back(mk<EQ>(n_lhs, n_rhs));
              }
              else {
                for (auto const& pair : args) {
                  res.push_back(mk<EQ>(pair.first, pair.second));
                }
              }
            }
            else {
              assert(!entry.second.empty());
              auto const& pair = entry.second[0];
              res.push_back(mk<EQ>(pair.first, pair.second));
            }
          }
          res.insert(res.end(), boundary, end);
          Expr ret = conjoin(res, exp->getFactory());
          return ret;
        }
      }
      {
        Expr isZero = bv::toIsZero(exp);
        if (isZero) {
          assert(isOpX<EQ>(isZero) && isOpX<BEXTRACT>(isZero->left()));
          Expr extr = isZero->left();
          Expr arg = bv::earg(extr);
          auto it = bitwidths.find(arg);
          assert(it != bitwidths.end());
          if (bv::width(isZero->right()->right()) == it->second) {
            // extracting all bits -> just remove the extract
            return mk<EQ>(arg, isZero->right());
          }
          return isZero;
        }
      }

      return exp;
    }

  private:
    bool isZeroBV(Expr e) { return bv::is_bvnum(e) && e->first() == zero; }
    bool isOneBV(Expr e) { return bv::is_bvnum(e) && e->first() == one; }

    void getBitWidth(Expr e) {
//        std::cout << "Called for " << *e << std::endl;
      if (bv::is_bvvar(e) || bv::is_bvnum(e)) {
        Expr sort = e->right();
        bitwidths[e] = bv::width(sort);
        return;
      }
      if (bv::is_bvconst(e)) {
        Expr sort = e->first()->right();
        bitwidths[e] = bv::width(sort);
        return;
      }
      if (isOpX<BAND>(e) || isOpX<BOR>(e) || isOpX<BADD>(e) || isOpX<BSUB>(e)
          || isOpX<BMUL>(e)) // TODO: add all; check BVMUL!
      {
        Expr e1 = e->left();
        Expr e2 = e->right();
        assert(bitwidths.find(e1) != bitwidths.end()
               && bitwidths.find(e2) != bitwidths.end()
               && bitwidths[e1] == bitwidths[e2]);

        bitwidths[e] = bitwidths[e1];
      }
      else if (isOpX<BNOT>(e)) {
        Expr arg = e->first();
        assert(bitwidths.find(arg) != bitwidths.end());
        bitwidths[e] = bitwidths[arg];
      }
      else if (isOpX<BEXTRACT>(e)) {
        auto h = bv::high(e);
        auto l = bv::low(e);
        assert(h >= l);
        int res = h - l + 1;
        bitwidths[e] = res;
      }
      else if (isOpX<ITE>(e)) {
        Expr e1 = e->arg(1);
        Expr e2 = e->arg(2);
        if (bitwidths.find(e1) != bitwidths.end()
            && bitwidths.find(e2) != bitwidths.end()
            && bitwidths[e1] == bitwidths[e2])
        {
          bitwidths[e] = bitwidths[e1];
        }
      }
      else if (isOpX<BCONCAT>(e)) {
        assert(e->arity() == 2); // MB: Can be different?
        Expr e1 = e->arg(0);
        Expr e2 = e->arg(1);
        auto it1 = bitwidths.find(e1);
        auto it2 = bitwidths.find(e2);
        assert(it1 != bitwidths.end() && it2 != bitwidths.end());
        if (it1 != bitwidths.end()
           && it2 != bitwidths.end()
           )
        {
          bitwidths[e] = bitwidths[e1] + bitwidths[e2];
        }
      }
    }
  };

  inline static Expr simplifyArithm (Expr exp)
  {
    RW<SimplifyArithmExpr> rw(new SimplifyArithmExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }
  
  inline static Expr simplifyBool (Expr exp)
  {
    RW<SimplifyBoolExpr> rw(new SimplifyBoolExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }

  inline static void simplBoolReplCnjHlp(ExprVector& hardVars, ExprSet& cnjs, ExprVector& facts, ExprVector& repls)
  {
    bool toRestart;
    ExprSet toInsert;

    for (auto it = cnjs.begin(); it != cnjs.end(); )
    {
      if (isOpX<TRUE>(*it))
      {
        it = cnjs.erase(it);
        continue;
      }

      if (isOpX<NEG>(*it))
      {
        Expr negged = mkNeg((*it)->left());
        it = cnjs.erase(it);
        cnjs.insert(negged);
        continue;
      }

      Expr a = replaceAll(*it, facts, repls);

      if (isOpX<IMPL>(a))
      {
        Expr lhs = simplifyBool(a->left());
        bool isTrue = isOpX<TRUE>(lhs);
        bool isFalse = isOpX<FALSE>(lhs);

        if (isTrue) a = simplifyBool(a->right());
        else if (isFalse) continue;
      }

      if (isOpX<EQ>(a))
      {
        // TODO: this could be symmetric

        Expr lhs = simplifyBool(a->left());
        bool isTrue = isOpX<TRUE>(lhs);
        bool isFalse = isOpX<FALSE>(lhs);

        if (isTrue) a = simplifyBool(a->right());
        else if (isFalse)
        {
          a = simplifyBool(mk<NEG>(a->right()));
        }
      }

      ExprSet splitted;
      getConj(a, splitted);
      toRestart = false;

      for (auto & c : splitted)
      {
        if (bind::isBoolConst(c))
        {
          bool nothard = find(hardVars.begin(), hardVars.end(), c) == hardVars.end();
          if (nothard)
          {
            toRestart = true;
            facts.push_back(c);
            repls.push_back(mk<TRUE>(a->getFactory()));
            facts.push_back(mk<NEG>(c));
            repls.push_back(mk<FALSE>(a->getFactory()));
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else if (isOpX<NEG>(c) && bind::isBoolConst(c->left()))
        {
          bool nothardLeft = find(hardVars.begin(), hardVars.end(), c->left()) == hardVars.end();
          if (nothardLeft)
          {
            toRestart = true;
            facts.push_back(c);
            repls.push_back(mk<TRUE>(a->getFactory()));
            facts.push_back(c->left());
            repls.push_back(mk<FALSE>(a->getFactory()));
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else if (isOpX<EQ>(c))
        {
          if (bind::isIntConst(c->left())  &&
              find(hardVars.begin(), hardVars.end(), c->left()) == hardVars.end())
          {
            toRestart = true;
            facts.push_back(c->left());
            repls.push_back(c->right());
          }
          else if (bind::isIntConst(c->right())  &&
                   find(hardVars.begin(), hardVars.end(), c->right()) == hardVars.end())
          {
            toRestart = true;
            facts.push_back(c->right());
            repls.push_back(c->left());
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else
        {
          toInsert.insert(c);
        }
      }

      it = cnjs.erase(it);
      if (toRestart) break;
    }

    cnjs.insert(toInsert.begin(), toInsert.end());
    if (toRestart)
    {
      simplBoolReplCnjHlp(hardVars, cnjs, facts, repls);
    }
  }

  // simplification based on boolean replacements
  inline static void simplBoolReplCnj(ExprVector& hardVars, ExprSet& cnjs)
  {
    ExprVector facts;
    ExprVector repls;
    simplBoolReplCnjHlp(hardVars, cnjs, facts, repls);
  }

  inline static ExprSet minusSets(ExprSet& v1, ExprSet& v2){
    ExprSet v3;
    bool res;
    for (auto &var1: v1){
      res = true;
      for (auto &var2: v2){
        if (var1 == var2) { res = false; break;}
      }
      if (res) v3.insert(var1);
    }
    return v3;
  }
  
  template<typename Range> static int getVarIndex(Expr var, Range& vec)
  {
    int i = 0;
    for (auto &e: vec)
    {
      if (var == e) return i;
      i++;
    }
    return -1;
  }
  
  static void getAddTerm (Expr a, ExprVector &terms); // declaration only
  
  inline static Expr arithmInverse(Expr e)
  {
    bool success = true;
    if (isOpX<MULT>(e))
    {
      int coef = 1;
      ExprVector ops;
      getMultOps (e, ops);

      Expr var = NULL;
      for (auto & a : ops)
      {
        if (isNumericConst(a))
        {
          coef *= lexical_cast<int>(a);
        }
        else if (bind::isIntConst(a) && var == NULL)
        {
          var = a;
        }
        else
        {
          success = false;
        }
      }
      if (success && coef != 0) return mk<MULT>(mkTerm (mpz_class (-coef), e->getFactory()), e->right());
      if (coef == 0) return mkTerm (mpz_class (0), e->getFactory());
    }
    else if (isOpX<PLUS>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        getAddTerm(arithmInverse(*it), terms);
      }
      return mknary<PLUS>(terms);
    }
    else if (isOpX<MINUS>(e))
    {
      ExprVector terms;
      getAddTerm(arithmInverse(*e->args_begin ()), terms);
      auto it = e->args_begin () + 1;
      for (auto end = e->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
      return mknary<PLUS>(terms);
    }
    else if (isOpX<UN_MINUS>(e))
    {
      return e->left();
    }
    else if (isNumericConst(e))
    {
      return mkTerm (mpz_class (-lexical_cast<int>(e)), e->getFactory());
    }
    return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);
  }
  
  inline static void getAddTerm (Expr a, ExprVector &terms) // implementation (mutually recursive)
  {
    if (isOpX<PLUS>(a))
    {
      for (auto it = a->args_begin (), end = a->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
    }
    else if (isOpX<MINUS>(a))
    {
      auto it = a->args_begin ();
      auto end = a->args_end ();
      getAddTerm(*it, terms);
      ++it;
      for (; it != end; ++it)
      {
        getAddTerm(arithmInverse(*it), terms);
      }
    }
    else if (isOpX<UN_MINUS>(a))
    {
      getAddTerm(arithmInverse(a->left()), terms);
    }
    else
    {
      terms.push_back(a);
    }
  }
  
  struct AddMultDistr
  {
    AddMultDistr () {};
    
    Expr operator() (Expr exp)
    {
      if (isOpX<MULT>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        
        ExprVector alllhs;
        getAddTerm(lhs, alllhs);
        
        ExprVector allrhs;
        getAddTerm(rhs, allrhs);
        
        ExprVector unf;
        for (auto &a : alllhs)
        {
          for (auto &b : allrhs)
          {
            unf.push_back(mk<MULT>(a, b));
          }
        }
        return mkplus(unf, exp->getFactory());
      }
      
      return exp;
    }
  };
  
  inline static Expr rewriteMultAdd (Expr exp)
  {
    RW<AddMultDistr> mu(new AddMultDistr());
    return dagVisit (mu, exp);
  }
  
  struct FindNonlinAndRewrite
  {
    ExprVector& vars;
    ExprMap& extraVars;
    
    FindNonlinAndRewrite (ExprVector& _vars, ExprMap& _extraVars) :
      vars(_vars), extraVars(_extraVars) {};
    
    Expr operator() (Expr t)
    {
      if (isOpX<MULT>(t))
      {
        // using the communativity of multiplication
        ExprVector ops;
        getMultOps(t, ops);

        ExprVector nonlinPart;
        int linPart = 1;
        for (auto & a : ops)
        {
          ExprVector av;
          filter (a, bind::IsConst (), inserter(av, av.begin()));
          if (av.size() == 0)
          {
            linPart = linPart * lexical_cast<int>(a);
            continue;
          }
          for (auto & b : av)
          {
            if (find(vars.begin(), vars.end(), b) == vars.end())
            {
              bool found = false;
              for (auto & c : extraVars) if (c.second == b) { found = true; break; }
              if (! found)
              {
                outs () << "WARNING. Wrong symbol at " << *t << ".\n";
                return mk<TRUE>(t->getFactory());
              }
            }
          }
          nonlinPart.push_back(a);
        }

        if (linPart == 0) return mkTerm (mpz_class (0), t->getFactory());
        if (nonlinPart.size() <= 1) return t;

        Expr multedVars = mkmult(nonlinPart, t->getFactory());
        if (extraVars[multedVars] == NULL)
        {
          Expr new_name = mkTerm<string> ("__e__" + to_string(extraVars.size()), t->getFactory());
          Expr var = bind::intConst(new_name);
          extraVars[multedVars] = var;
        }

        if (linPart == 1) return extraVars[multedVars];
        else return mk<MULT>( mkTerm (mpz_class (linPart), t->getFactory()), extraVars[multedVars]);
      }
      else if (isOpX<MOD>(t) || isOpX<IDIV>(t) || isOpX<DIV>(t))
      {
        int indl = getVarIndex(t->left(), vars);
        int indr = getVarIndex(t->right(), vars);

        Expr key = t;
        if (indl >= 0) key = replaceAll(key, t->left(), vars[indl]);
        if (indr >= 0) key = replaceAll(key, t->right(), vars[indr]);

        if (isOpX<MPZ>(t->left()) && lexical_cast<int>(t->left()) == 0)
          return mkTerm (mpz_class (0), t->getFactory());

        if (extraVars[key] == NULL)
        {
          Expr new_name = mkTerm<string> ("__e__" + to_string(extraVars.size()), t->getFactory());
          Expr var = bind::intConst(new_name);
          extraVars[key] = var;
        }
        return extraVars[key];
      }
      return t;
    }
  };

  inline static Expr findNonlinAndRewrite (Expr exp, ExprVector& vars, ExprMap& extraVars)
  {
    RW<FindNonlinAndRewrite> mu(new FindNonlinAndRewrite(vars, extraVars));
    return dagVisit (mu, exp);
  }

  struct FindNonlin : public std::unary_function<Expr, VisitAction>
  {
    bool found;

    FindNonlin () : found (false) {}

    VisitAction operator() (Expr exp)
    {
      if (found)
      {
        found = true;
        return VisitAction::skipKids ();
      }
      else if (isOpX<MULT>(exp) || isOpX<MOD>(exp) || isOpX<DIV>(exp) || isOpX<IDIV>(exp))
      {
        int v = 0;
        for (unsigned j = 0; j < exp->arity(); j++)
        {
          Expr q = exp->arg(j);
          if (bind::isIntConst(q)) v++;     // GF: a simple counter, to extend
        }

        if (v > 1)
        {
          found = true;
          return VisitAction::skipKids ();
        }
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findNonlin (Expr e1)
  {
    FindNonlin fn;
    dagVisit (fn, e1);
    return fn.found;
  }

  struct FindArray : public std::unary_function<Expr, VisitAction>
  {
    bool found;

    FindArray () : found (false) {}

    VisitAction operator() (Expr exp)
    {
      if (found)
      {
        return VisitAction::skipKids ();
      }
      else if (bind::isConst<ARRAY_TY> (exp))
      {
        found = true;
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findArray (Expr e1)
  {
    FindArray fn;
    dagVisit (fn, e1);
    return fn.found;
  }

  inline static Expr simplifiedAnd (Expr a, Expr b){
    ExprSet conjs;
    getConj(a, conjs);
    getConj(b, conjs);
    return
    (conjs.size() == 0) ? mk<TRUE>(a->getFactory()) :
    (conjs.size() == 1) ? *conjs.begin() :
    mknary<AND>(conjs);
  }

  inline int intersectSize(ExprVector& a, ExprVector& b){
    ExprSet c;
    for (auto &var: a)
      if (find(b.begin(), b.end(), var) != b.end()) c.insert(var);
    return c.size();
  }

  inline static Expr simplifyArithmDisjunctions(Expr term);

  inline static void productAnd (ExprSet& as, ExprSet& bs, ExprSet& ps)
  {
    for (auto &a : as)
    {
      for (auto &b : bs)
      {
        Expr orredExpr = simplifyArithmDisjunctions(mk<OR>(a, b));
        if (!isOpX<TRUE>(orredExpr))
          ps.insert(orredExpr);
      }
    }
  }

  // ab \/ cde \/ f =>
  //                    (a \/ c \/ f) /\ (a \/ d \/ f) /\ (a \/ e \/ f) /\
  //                    (b \/ c \/ f) /\ (b \/ d \/ f) /\ (b \/ e \/ f)
  inline static Expr rewriteOrAnd(Expr exp, bool approx = false)
  {
    int maxConjs = 0;
    ExprSet disjs;
    getDisj(exp, disjs);
    if (disjs.size() == 1)
      return disjoin(disjs, exp->getFactory());
    
    vector<ExprSet> dconjs;
    for (auto &a : disjs)
    {
      ExprSet conjs;
      getConj(a, conjs);
      dconjs.push_back(conjs);
      if (maxConjs < conjs.size()) maxConjs = conjs.size();
    }

    if (disjs.size() > 3 && maxConjs > 3)
    {
      approx = true;
    }

    if (approx)
    {
      ExprSet newDisjs;
      for (auto &d : dconjs)
        for (auto &c : d)
          newDisjs.insert(c);
      return disjoin(newDisjs, exp->getFactory());
    }

    ExprSet older;
    productAnd(dconjs[0], dconjs[1], older);

    ExprSet newer = older;
    for (int i = 2; i < disjs.size(); i++)
    {
      newer.clear();
      productAnd(dconjs[i], older, newer);
      older = newer;
    }
    return conjoin (newer, exp->getFactory());
  }

  inline static Expr cloneVar(Expr var, Expr new_name) // ... and give a new_name to the clone
  {
    if (bind::isIntConst(var))
      return bind::intConst(new_name);
    else if (bind::isRealConst(var))
      return bind::realConst(new_name);
    else if (bind::isBoolConst(var))
      return bind::boolConst(new_name);
    else if (bind::isConst<ARRAY_TY> (var))
      return bind::mkConst(new_name, mk<ARRAY_TY> (
             mk<INT_TY> (new_name->getFactory()),
             mk<INT_TY> (new_name->getFactory()))); // GF: currently, only Arrays over Ints
    else if (bv::is_bvconst(var))
      return bv::bvConst(new_name, bv::width(var->first()->arg(1)));

    else return NULL;
  }

  // not very pretty method, but..
  inline static Expr reBuildCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<LEQ>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    if (isOpX<GT>(term))
    {
      return mk<GT>(lhs, rhs);
    }
    if (isOpX<BULE>(term))
    {
      return bv::bvule(lhs, rhs);
    }
    if (isOpX<BULT>(term))
    {
      return bv::bvult(lhs, rhs);
    }
    if (isOpX<BUGE>(term))
    {
      return bv::bvuge(lhs, rhs);
    }
    if (isOpX<BUGT>(term))
    {
      return bv::bvugt(lhs, rhs);
    }
    if (isOpX<BSLE>(term))
    {
      return bv::bvsle(lhs, rhs);
    }
    if (isOpX<BSLT>(term))
    {
      return bv::bvslt(lhs, rhs);
    }
    if (isOpX<BSGE>(term))
    {
      return bv::bvsge(lhs, rhs);
    }
    if (isOpX<BSGT>(term))
    {
      return bv::bvsgt(lhs, rhs);
    }
    assert(false);
  }
  
  inline static Expr reBuildNegCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<GT>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<LEQ>(lhs, rhs);
  }
  
  // not very pretty method, but..
  inline static bool evaluateCmpConsts(Expr term, int a, int b)
  {
    if (isOpX<EQ>(term))
    {
      return (a == b);
    }
    if (isOpX<NEQ>(term))
    {
      return (a != b);
    }
    if (isOpX<LEQ>(term))
    {
      return (a <= b);
    }
    if (isOpX<GEQ>(term))
    {
      return (a >= b);
    }
    if (isOpX<LT>(term))
    {
      return (a < b);
    }
    assert(isOpX<GT>(term));
    return (a > b);
  }
  
  inline static Expr mkNeg(Expr term)
  {
    if (isOpX<TRUE>(term)) { return mk<FALSE>(term->getFactory()); }
    if (isOpX<FALSE>(term)) { return mk<TRUE>(term->getFactory()); }
    if (isOpX<NEG>(term))
    {
      return term->arg(0);
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(mkNeg(term->arg(i)));
      }
      return isOpX<AND>(term) ? disjoin(args, term->getFactory()) :
                                conjoin (args, term->getFactory());
    }
    else if (isOp<ComparissonOp>(term))
    {
      return reBuildNegCmp(term, term->arg(0), term->arg(1));
    }
    else if (isOpX<IMPL>(term))
    {
      return mk<AND>(term->left(), mkNeg(term->right()));
    }
    else if (isOpX<FORALL>(term))
    {
      return mkNeg(term->last());
    }
    return mk<NEG>(term);
  }

  inline static Expr convertToGEandGT(Expr term)
  {
    if (isOpX<LT>(term)) return mk<GT>(term->right(), term->left());

    if (isOpX<LEQ>(term)) return mk<GEQ>(term->right(), term->left());

    if (isOpX<EQ>(term))
    {
      if (hasBoolSort(term->left())) return
          mk<OR>(mk<AND>(term->left(), term->right()),
                 mk<AND>(mkNeg(term->left()), mkNeg(term->right())));
      else if (isNumeric(term->left())) return mk<AND>(
          mk<GEQ>(term->left(), term->right()),
          mk<GEQ>(term->right(), term->left()));
      else return term;
    }

    if (isOpX<NEQ>(term))
    {
      if (hasBoolSort(term->left())) return
          mk<OR>(mk<AND>(term->left(), mkNeg(term->right())),
                 mk<AND>(mkNeg(term->left()), term->right()));
      else if (isNumeric(term->left())) return mk<OR>(
          mk<GT>(term->left(), term->right()),
          mk<GT>(term->right(), term->left()));
      else return term;
    }

    if (isOpX<NEG>(term))
    {
      return mk<NEG>(convertToGEandGT(term->last()));
    }

    if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(convertToGEandGT(term->arg(i)));
      }

      return isOpX<AND>(term) ? conjoin (args, term->getFactory()) :
        disjoin (args, term->getFactory());

    }
    return term;
  }

  Expr convertBVToLeqAndLt(Expr e) {
    assert(bv::isBVComparison(e));
    if (isOpX<BULE>(e) || isOpX<BULT>(e) || isOpX<BSLE>(e) || isOpX<BSLT>(e)) {
      return e;
    }
    if (isOpX<BUGE>(e)) { return bv::bvule(e->right(), e->left()); }
    if (isOpX<BUGT>(e)) { return bv::bvult(e->right(), e->left()); }
    if (isOpX<BSGE>(e)) { return bv::bvsle(e->right(), e->left()); }
    if (isOpX<BSGT>(e)) { return bv::bvslt(e->right(), e->left()); }
    return nullptr;
  }

  /* find expressions of type expr = arrayVar in e and store it in output */
  inline static void getArrayEqualExprs(Expr e, Expr arrayVar, ExprVector & output)
  {
    if (e->arity() == 1) {
      return;

    } else if (e->arity() == 2) {
      Expr lhs = e->left();
      Expr rhs = e->right();
      if (lhs == arrayVar) {
        output.push_back(rhs);
        return;

      } else if (rhs == arrayVar) {
        output.push_back(lhs);
        return;
      }
    }

    for (int i = 0; i < e->arity(); i++) {
      getArrayEqualExprs(e->arg(i), arrayVar, output);
    }
  }

  /* find all expressions in e of type expr = arrayVar */
  /* and replace it by STORE(expr, itr, val) = arrayVar*/
  inline static Expr propagateStore(Expr e, Expr itr, Expr val, Expr arrayVar)
  {
    Expr retExpr = e;
    ExprVector exprvec;
    getArrayEqualExprs(e, arrayVar, exprvec);
    for (auto & ev : exprvec)
      retExpr = replaceAll(retExpr, ev, mk<STORE>(ev, itr, val));
    return retExpr;
  }

  inline static Expr unfoldITE(Expr term)
  {
    if (isOpX<ITE>(term))
    {
      Expr iteCond = unfoldITE (term->arg(0));
      Expr iteC1 = unfoldITE (term->arg(1));
      Expr iteC2 = unfoldITE (term->arg(2));
      
      return mk<OR>( mk<AND>(iteCond, iteC1),
                    mk<AND>(mkNeg(iteCond), iteC2));
    }
    else if (isOpX<NEG>(term))
    {
      return mkNeg(unfoldITE(term->last()));
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(unfoldITE(term->arg(i)));
      }
      return isOpX<AND>(term) ? conjoin (args, term->getFactory()) :
                                disjoin (args, term->getFactory());
    }
    else if (isOp<ComparissonOp>(term))
    {
      Expr lhs = term->arg(0);
      Expr rhs = term->arg(1);
      
      if (isOpX<ITE>(rhs))
      {
        Expr iteCond = unfoldITE (rhs->arg(0));
        Expr iteC1 = rhs->arg(1);
        Expr iteC2 = rhs->arg(2);
        
        Expr newCmp1 = unfoldITE (reBuildCmp(term, lhs, iteC1));
        Expr newCmp2 = unfoldITE (reBuildCmp(term, lhs, iteC2));
        
        Expr transformed = mk<OR>( mk<AND>(iteCond, newCmp1),
                                  mk<AND>(mkNeg(iteCond), newCmp2));
        
        //          outs () << "     [1b] ---> " << *term << "\n";
        //          outs () << "     [1e] ---> " << *transformed << "\n\n";
        return transformed;
      }
      else if (isOpX<ITE>(lhs))
      {
        // GF: symmetric case to the one above
        
        Expr iteCond = unfoldITE (lhs->arg(0));
        Expr iteC1 = lhs->arg(1);
        Expr iteC2 = lhs->arg(2);
        
        Expr newCmp1 = unfoldITE (reBuildCmp(term, iteC1, rhs));
        Expr newCmp2 = unfoldITE (reBuildCmp(term, iteC2, rhs));
        
        Expr transformed = mk<OR>( mk<AND>(iteCond, newCmp1),
                                  mk<AND>(mkNeg(iteCond), newCmp2));
        
        //          outs () << "    [2b] ---> " << *term << "\n";
        //          outs () << "    [2e] ---> " << *transformed << "\n\n";
        return transformed;
      }
      if (isOpX<PLUS>(rhs))
      {
        bool found = false;
        Expr iteArg;
        ExprVector newArgs;
        for (auto it = rhs->args_begin(), end = rhs->args_end(); it != end; ++it)
        {
          // make sure that only one ITE is found
          
          if (!found && isOpX<ITE>(*it))
          {
            found = true;
            iteArg = *it;
          }
          else
          {
            newArgs.push_back(*it);
          }
        }
        if (found)
        {
          Expr iteCond = unfoldITE (iteArg->arg(0));
          Expr iteC1 = iteArg->arg(1);
          Expr iteC2 = iteArg->arg(2);
          
          newArgs.push_back(iteC1);
          Expr e1 = unfoldITE (reBuildCmp(term, lhs, mknary<PLUS>(newArgs))); // GF: "unfoldITE" gives error...
          
          newArgs.pop_back();
          newArgs.push_back(iteC2);
          Expr e2 = unfoldITE (reBuildCmp(term, lhs, mknary<PLUS>(newArgs)));
          
          Expr transformed = mk<OR>(mk<AND>(iteCond, e1),
                                    mk<AND>(mkNeg(iteCond),e2));
          
          //            outs () << "    [3b] ---> " << *term << "\n";
          //            outs () << "    [3e] ---> " << *transformed << "\n\n";
          
          return transformed;
        }
      }
      if (isOpX<PLUS>(lhs))
      {
        // symmetric to the above case
        bool found = false;
        Expr iteArg;
        ExprVector newArgs;
        for (auto it = lhs->args_begin(), end = lhs->args_end(); it != end; ++it)
        {
          if (!found && isOpX<ITE>(*it))
          {
            found = true;
            iteArg = *it;
          }
          else
          {
            newArgs.push_back(*it);
          }
        }
        
        if (found)
        {
          Expr iteCond = unfoldITE (iteArg->arg(0));
          Expr iteC1 = iteArg->arg(1);
          Expr iteC2 = iteArg->arg(2);
          
          newArgs.push_back(iteC1);
          Expr e1 = unfoldITE (reBuildCmp(term, mknary<PLUS>(newArgs), rhs));
          
          newArgs.pop_back();
          newArgs.push_back(iteC2);
          Expr e2 = unfoldITE (reBuildCmp(term, mknary<PLUS>(newArgs), rhs));
          
          Expr transformed = mk<OR>(mk<AND>(iteCond,e1),
                                    mk<AND>(mkNeg(iteCond),e2));
          
          //            outs () << "    [4b] ---> " << *term << "\n";
          //            outs () << "    [4e] ---> " << *transformed << "\n\n";
          
          return transformed;
        }
      }
      if (isOpX<STORE>(lhs))
      {
        Expr arrVar = lhs->left();
        if (isOpX<ITE>(arrVar))
        {
          Expr ifExpr =  unfoldITE(reBuildCmp(term, arrVar->right(), rhs));
          Expr elseExpr = unfoldITE(reBuildCmp(term, arrVar->last(), rhs));

          ifExpr = propagateStore(ifExpr, lhs->right(), lhs->last(), rhs);
          elseExpr = propagateStore(elseExpr, lhs->right(), lhs->last(), rhs);

          Expr condExpr = unfoldITE (arrVar->left());
          Expr retExpr = mk<OR> (mk<AND>(condExpr, ifExpr), mk<AND>(mkNeg(condExpr), elseExpr));

          return retExpr;
        }
      }
      if (isOpX<STORE>(rhs))
      {
        Expr arrVar = rhs->left();
        if (isOpX<ITE>(arrVar))
        {
          Expr ifExpr = unfoldITE (reBuildCmp(term, arrVar->right(), lhs));
          Expr elseExpr = unfoldITE (reBuildCmp(term, arrVar->last(), lhs));

          ifExpr = propagateStore(ifExpr, rhs->right(), rhs->last(), lhs);
          elseExpr = propagateStore(elseExpr, rhs->right(), rhs->last(), lhs);

          Expr condExpr = unfoldITE (arrVar->left());
          Expr retExpr = mk<OR> (mk<AND>(condExpr, ifExpr), mk<AND>(mkNeg(condExpr), elseExpr));

          return retExpr;
        }
      }
      if (isOpX<SELECT>(rhs))
      {
        Expr arrVar = rhs->left();
        if (isOpX<ITE>(arrVar))
        {
          return unfoldITE (reBuildCmp(term,
                 mk<ITE>(arrVar->left(),
                         mk<SELECT>(arrVar->right(), rhs->right()),
                         mk<SELECT>(arrVar->last(), rhs->right())), lhs));
        }
      }
    }
    return term;
  }
  
  struct MoveInsideITEr
  {
    MoveInsideITEr () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<MOD>(exp))
      {
        Expr ite = exp->arg(0);
        if (isOpX<ITE>(ite))
        {
          return mk<ITE>(ite->arg(0),
                         mk<MOD>(ite->arg(1), exp->arg(1)),
                         mk<MOD>(ite->arg(2), exp->arg(1)));
        }
      }
      if (isOpX<MULT>(exp))
      {
        ExprVector args;
        Expr ite;
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it)
        {
          if (isOpX<ITE>(*it))
          {
            if (ite != NULL) return exp;
            ite = *it;
          }
          else
          {
            args.push_back(*it);
          }
        }

        if (ite == NULL) return exp;

        Expr multiplier = mkmult (args, exp->getFactory());
        return mk<ITE>(ite->arg(0),
                       mk<MULT>(multiplier, ite->arg(1)),
                       mk<MULT>(multiplier, ite->arg(2)));
      }

      return exp;
    }
  };

  inline static Expr moveInsideITE (Expr exp)
  {
    RW<MoveInsideITEr> a(new MoveInsideITEr());
    return dagVisit (a, exp);
  }

  struct RAVSUBEXPR: public std::unary_function<Expr,VisitAction>
  {
    Expr s;
    Expr t;
    Expr p;

    RAVSUBEXPR (Expr _s, Expr _t, Expr _p) : s(_s), t(_t), p(_p) {}
    VisitAction operator() (Expr exp) const
    {
      return exp == s ?
        VisitAction::changeTo (replaceAll(exp, t, p)) :
        VisitAction::doKids ();
    }
  };

  // -- replace all occurrences of t by p in a subexpression s  of exp
  inline Expr replaceInSubexpr (Expr exp, Expr s, Expr t, Expr p)
  {
    RAVSUBEXPR rav(s, t, p);
    return dagVisit (rav, exp);
  }

  struct NegAndRewriter
  {
    NegAndRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<NEG>(exp) && isOpX<AND>(exp->arg(0)))
      {
        ExprSet cnjs;
        getConj(exp->arg(0), cnjs);
        ExprSet neggedCnjs;
        for (auto & c : cnjs) neggedCnjs.insert(mkNeg(c));
        return disjoin(neggedCnjs, exp->getFactory());
      }
      return exp;
    }
  };

  inline static Expr rewriteSelectStore(Expr exp);

  struct SelectStoreRewriter
  {
    SelectStoreRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<SELECT>(exp) && isOpX<STORE>(exp->left()))
      {
        if (exp->right() == exp->left()->right())
          return exp->left()->last();
        else
          return mk<ITE>(mk<EQ>(exp->right(), exp->left()->right()),
             exp->left()->last(), mk<SELECT>(exp->left()->left(), exp->right()));
      }
      if (isOpX<EQ>(exp) && isOpX<STORE>(exp->right()))
      {
        ExprSet tmp;
        tmp.insert(rewriteSelectStore(mk<EQ>(exp->left(), exp->right()->left())));
        tmp.insert(mk<EQ>(exp->right()->last(), mk<SELECT>(exp->left(), exp->right()->right())));
        return conjoin (tmp, exp->getFactory());
      }
      if (isOpX<EQ>(exp) && isOpX<STORE>(exp->left()))
      {
        ExprSet tmp;
        tmp.insert(rewriteSelectStore(mk<EQ>(exp->right(), exp->left()->left())));
        tmp.insert(mk<EQ>(exp->left()->last(), mk<SELECT>(exp->right(), exp->left()->right())));
        return conjoin (tmp, exp->getFactory());
      }
      return exp;
    }
  };

  struct SelectReplacer : public std::unary_function<Expr, VisitAction>
  {
    ExprMap& sels;
    SelectReplacer (ExprMap& _sels) :  sels(_sels) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<SELECT>(exp))
      {
        if (sels[exp] != NULL) return sels[exp];
        Expr repl = bind::intConst(mkTerm<string> ("sel_" + lexical_cast<string>(sels.size()), exp->getFactory()));
        sels[exp] = repl;
        return repl;
      }
      return exp;
    }
  };

  inline static Expr replaceSelects(Expr exp, ExprMap& sels)
  {
    RW<SelectReplacer> a(new SelectReplacer(sels));
    return dagVisit (a, exp);
  }

  struct QuantifiedVarsFilter : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& vars;

    QuantifiedVarsFilter (ExprSet& _vars): vars(_vars) {};

    VisitAction operator() (Expr exp)
    {
      if (isOp<FORALL>(exp))
      {
        for (int i = 0; i < exp->arity() - 1; i++)
        {
          vars.insert(bind::fapp(exp->arg(i)));
        }
      }
      return VisitAction::doKids ();
    }
  };

  inline void getQuantifiedVars (Expr exp, ExprSet& vars)
  {
    QuantifiedVarsFilter qe (vars);
    dagVisit (qe, exp);
  }

  template<typename Range> static void update_min_value(ExprMap& m, Expr key, Expr value, Range& quantified, ExprSet& newCnjs)
  {
    // just heuristic
    if (m[key] == NULL)
    {
      m[key] = value;
    }
    else if (emptyIntersect(value, quantified) || treeSize(value) < treeSize(m[key]))
    {
      newCnjs.insert(mk<EQ>(key, m[key]));
      m[key] = value;
    }
    else
    {
      newCnjs.insert(mk<EQ>(key, value));
    }
  }

  template<typename Range> static Expr simpleQE(Expr exp, Range& quantified, bool removeUsed = true, bool strict = true)
  {
    // rewrite just equalities
    ExprSet cnjs;
    ExprSet newCnjs;
    ExprMap eqs;
    getConj(exp, cnjs);
    for (auto & a : cnjs)
    {
      bool eq = false;
      if (isOpX<EQ>(a))
      {
        for (auto & b : quantified)
        {
          if (a->left() == b && (!strict || emptyIntersect(a->right(), quantified)))
          {
            eq = true;
            update_min_value(eqs, b, a->right(), quantified, newCnjs);
            break;
          }
          else if (a->right() == b && (!strict || emptyIntersect(a->left(), quantified)))
          {
            eq = true;
            update_min_value(eqs, b, a->left(), quantified, newCnjs);
            break;
          }
        }
      }
      if (!eq)
      {
        newCnjs.insert(a);
      }
    }

    Expr qed = conjoin(newCnjs, exp->getFactory());
    ExprSet used;
    while (true)
    {
      bool toBreak = true;
      for (auto & a : eqs)
      {
        if (a.first == NULL || a.second == NULL) continue;
        if (!emptyIntersect(a.first, qed))
        {
          qed = replaceAll(qed, a.first, a.second);
          if (removeUsed) used.insert(a.first);
          toBreak = false;
        }
        for (auto & b : eqs)
        {
          if (a == b) continue;
          if (!emptyIntersect(a.first, b.second))
          {
            b.second = replaceAll(b.second, a.first, a.second);
          }
        }
      }
      if (toBreak) break;
    }

    newCnjs.clear();
    getConj(qed, newCnjs);
    if (strict)
    {
      for (auto it = newCnjs.begin(); it != newCnjs.end(); )
      if (emptyIntersect(*it, quantified)) ++it;
      else it = newCnjs.erase(it);
      return conjoin(newCnjs, exp->getFactory());
    }

    for (auto & a : eqs)
    {
      if (find(used.begin(), used.end(), a.first) == used.end())
        newCnjs.insert(mk<EQ>(a.first, a.second));
    }
    qed = conjoin(newCnjs, exp->getFactory());
    return qed;
//    if (!strict) return qed;
//
//    // check if there are some not eliminated vars
//    ExprVector av;
//    filter (qed, bind::IsConst (), inserter(av, av.begin()));
//    if (emptyIntersect(av, quantified)) return qed;
//
//    // otherwise result is incomplete
//    return mk<TRUE>(exp->getFactory());
  }

  struct QESubexpr
  {
    ExprVector& quantified;
    QESubexpr (ExprVector& _quantified): quantified(_quantified) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<AND>(exp) && !containsOp<OR>(exp))
      {
        return simpleQE(exp, quantified);
      }
      return exp;
    }
  };

  inline static Expr simpleQERecurs(Expr exp, ExprVector& quantified)
  {
    RW<QESubexpr> a(new QESubexpr(quantified));
    return dagVisit (a, exp);
  }

  inline static Expr rewriteNegAnd(Expr exp)
  {
    RW<NegAndRewriter> a(new NegAndRewriter());
    return dagVisit (a, exp);
  }

  inline static Expr rewriteSelectStore(Expr exp)
  {
    RW<SelectStoreRewriter> a(new SelectStoreRewriter());
    return dagVisit (a, exp);
  }

  // very simple check if tautology (SMT-based check is expensive)
  inline static bool isTautology(Expr term)
  {
    if (isOpX<EQ>(term))
      if (term->arg(0) == term->arg(1)) return true;

    if (isOp<ComparissonOp>(term))
      if (isNumericConst(term->arg(0)) && isNumericConst(term->arg(1)))
        return evaluateCmpConsts(term,
                                 lexical_cast<int>(term->arg(0)), lexical_cast<int>(term->arg(1)));

    ExprSet cnjs;
    getConj(term, cnjs);
    if (cnjs.size() < 2) return false;

    bool res = true;
    for (auto &a : cnjs) res &= isTautology(a);

    return res;
  }

  inline static bool isLinearCombination(Expr term)
  {
    // an approximation of..
    if (isNumericConst(term)) {
      return false;
    }
    else if (bind::isIntConst(term)) {
      return true;
    }
    else if (isOpX<MULT>(term)) {
      bool res = false;
      for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it){
        res = res || isLinearCombination(*it);
      }
      return res;
    }
    else if (isOpX<PLUS>(term) || isOpX<MINUS>(term) || isOpX<UN_MINUS>(term)) {
      bool res = true;
      for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it){
        res = res && isLinearCombination(*it);
      }
      return res;
    }
    return false;
  }

  inline static Expr simplifyArithmDisjunctions(Expr term)
  {
    // a simple simplifier; to be enhanced

    ExprSet dsjs;
    getDisj(term, dsjs);
    if (dsjs.size() < 2) return term;

    ExprSet vars;

    // search for a var, const*var or whatever exists in any disjunct
    for (auto & d : dsjs) {
      if (isOpX<TRUE>(d)) return d;

      if (!isOp<ComparissonOp>(d)) continue;

      Expr lhs = d->arg(0);
      Expr rhs = d->arg(1);
      if (isLinearCombination(lhs)) vars.insert(lhs);
      if (isLinearCombination(rhs)) vars.insert(rhs);
    }

    if (vars.size() == 0) return term;

    for (auto &var : vars) {

      int cur_min_gt = INT_MAX; // maintain several vars
      int cur_min_ge = INT_MAX; // to avoid introducing new constants
      int cur_max_lt = INT_MIN;
      int cur_max_le = INT_MIN;

      for (auto it = dsjs.begin(); it != dsjs.end(); ) {
        auto d = *it;

        if (!isOpX<GEQ>(d) && !isOpX<LEQ>(d) && !isOpX<GT>(d) && !isOpX<LT>(d)) { ++it; continue; }

        Expr rewritten = ineqMover(d, var);

        if (isNumericConst(rewritten->arg(0)) &&
            isNumericConst(rewritten->arg(1))) {

          if (evaluateCmpConsts(rewritten, lexical_cast<int>(rewritten->arg(0)),
                                           lexical_cast<int>(rewritten->arg(1)))){
            return mk<TRUE>(d->getFactory());
          } else {
            dsjs.erase(it++);
            continue;
          }
        }

        if (rewritten->arg(0) != var) {
          rewritten = ineqReverter(rewritten);
          if (rewritten->arg(0) != var) { ++it; continue; }
        }

        if (!isNumericConst(rewritten->arg(1))) { ++it; continue; }

        int c = lexical_cast<int>(rewritten->arg(1));

        if (isOpX<LEQ>(rewritten)) { cur_max_le = max(cur_max_le, c); }
        if (isOpX<GEQ>(rewritten)) { cur_min_ge = min(cur_min_ge, c); }
        if (isOpX<LT>(rewritten))  { cur_max_lt = max(cur_max_lt, c); }
        if (isOpX<GT>(rewritten))  { cur_min_gt = min(cur_min_gt, c); }

        if (max(cur_max_le+1, cur_max_lt) > min(cur_min_ge-1,cur_min_gt))
          return mk<TRUE>(term->getFactory());

        dsjs.erase(it++);
      }

      if (cur_min_ge != INT_MAX) {
        Expr minExpr = mk<GEQ>(var, mkTerm (mpz_class (cur_min_ge), term->getFactory()));
        dsjs.insert(minExpr);
      }
      if (cur_min_gt != INT_MAX) {
        Expr minExpr = mk<GT>(var, mkTerm (mpz_class (cur_min_gt), term->getFactory()));
        dsjs.insert(minExpr);
      }
      if (cur_max_le != INT_MIN) {
        Expr maxExpr = mk<LEQ>(var, mkTerm (mpz_class (cur_max_le), term->getFactory()));
        dsjs.insert(maxExpr);
      }
      if (cur_max_lt != INT_MIN) {
        Expr maxExpr = mk<LT>(var, mkTerm (mpz_class (cur_max_lt), term->getFactory()));
        dsjs.insert(maxExpr);
      }
    }

    return disjoin(dsjs, term->getFactory());
  }

  inline static Expr normalizeAtom(Expr term, ExprVector& intVars)
  {
    if (isOp<ComparissonOp>(term))
    {
      Expr lhs = term->left();
      Expr rhs = term->right();
      
      ExprVector all;
      ExprVector allrhs;
      
      getAddTerm(lhs, all);
      getAddTerm(rhs, allrhs);
      for (auto & a : allrhs)
      {
        all.push_back(arithmInverse(a));
      }
      ExprSet newlhs;
      for (auto &v : intVars)
      {
        int coef = 0;
        string s1 = lexical_cast<string>(v);
        for (auto it = all.begin(); it != all.end();)
        {
          string s2 = lexical_cast<string>(*it);

          if (s1 == s2)
          {
            coef++;
            it = all.erase(it);
          }
          else if (isOpX<UN_MINUS>(*it))
          {
            string s3 = lexical_cast<string>((*it)->left());
            if (s1 == s3)
            {
              coef--;
              it = all.erase(it);
            }
            else
            {
              ++it;
            }
          }
          else if (isOpX<MULT>(*it))
          {
            ExprVector ops;
            getMultOps (*it, ops);

            int c = 1;
            bool success = true;
            for (auto & a : ops)
            {
              if (s1 == lexical_cast<string>(a))
              {
                // all good!
              }
              else if (isOpX<MPZ>(a))
              {
                c = c * lexical_cast<int>(a);
              }
              else
              {
                ++it;
                success = false;
                break;
              }
            }
            if (success)
            {
              coef += c;
              it = all.erase(it);
            }
          }
          else
          {
            ++it;
          }
        }
        if (coef != 0) newlhs.insert(mk<MULT>(mkTerm (mpz_class (coef), term->getFactory()), v));
      }
      
      bool success = true;
      int intconst = 0;
      
      for (auto &e : all)
      {
        if (isNumericConst(e))
        {
          intconst += lexical_cast<int>(e);
        }
        else if (isOpX<MULT>(e))
        {
          // GF: sometimes it fails (no idea why)
          int thisTerm = 1;
          for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
          {
            if (isOpX<MPZ>(*it))
              thisTerm *= lexical_cast<int>(*it);
            else
              success = false;
          }
          intconst += thisTerm;
        }
        else
        {
          success = false;
        }
      }
      
      if (success && newlhs.size() == 0)
      {
        return (evaluateCmpConsts(term, 0, -intconst)) ? mk<TRUE>(term->getFactory()) :
                                                         mk<FALSE>(term->getFactory());
      }
      
      if (success)
      {
        Expr pl = (newlhs.size() == 1) ? *newlhs.begin(): mknary<PLUS>(newlhs);
        Expr c = mkTerm (mpz_class (-intconst), term->getFactory());
        return reBuildCmp(term, pl, c);
      }
    }
    return term;
  }
  
  inline static Expr normalizeDisj(Expr exp, ExprVector& intVars)
  {
    ExprSet disjs;
    ExprSet newDisjs;
    getDisj(exp, disjs);
    for (auto &d : disjs)
    {
      Expr norm = normalizeAtom(d, intVars);
      if ( isOpX<TRUE> (norm)) return norm;
      if (!isOpX<FALSE>(norm)) newDisjs.insert(norm);
    }
    return disjoin(newDisjs, exp->getFactory());
  }
  
  inline static bool getLinCombCoefs(Expr ex, set<int>& intCoefs)
  {
    bool res = true;
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        res = res && getLinCombCoefs(*it, intCoefs);
    }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      Expr lhs = ex->left();
      if (isOpX<PLUS>(lhs))
      {
        for (auto it = lhs->args_begin (), end = lhs->args_end (); it != end; ++it)
        {
          if (isOpX<MULT>(*it))           // else, it is 1, and we will add it anyway;
          {
            if (isOpX<MPZ>((*it)->left()))
              intCoefs.insert(lexical_cast<int> ((*it)->left()));
            else return false;
          }
        }
      }
      else if (isOpX<MULT>(lhs))
      {
        if (isOpX<MPZ>(lhs->left()))
          intCoefs.insert(lexical_cast<int> (lhs->left()));
        else return false;
      }
      else
      {
        return false;
      }
    }
    return res;
  }

  inline static void getLinCombConsts(Expr ex, set<int>& intConsts)
  {
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        getLinCombConsts(*it, intConsts);
      }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      intConsts.insert(lexical_cast<int> (ex->right()));
    }
  }

  inline static void normalizeSelects(Expr& body)
  {
    ExprVector se;
    filter (body, bind::IsSelect (), inserter(se, se.begin()));
    for (auto & s : se)
    {
      if (!bind::isIntConst(s->right()))
      {
        Expr var_it = bind::intConst(mkTerm<string> ("it_" + lexical_cast<string>(&s), body->getFactory()));
        body = mk<AND>(replaceInSubexpr(body, s, s->right(), var_it), mk<EQ>(s->right(), var_it));
      }
    }
  }

  inline static void uniqueizeSelects(Expr& body)
  {
    ExprVector se;
    filter (body, bind::IsSelect (), inserter(se, se.begin()));
    if (se.size() < 2) return;

    ExprSet seenIterators;
    for (auto & s : se)
    {
      if (find(seenIterators.begin(), seenIterators.end(), s->right()) == seenIterators.end())
      {
        seenIterators.insert(s->right());
      }
      else
      {
        Expr var_it = bind::intConst(mkTerm<string> ("it_" + lexical_cast<string>(&s), body->getFactory()));
        body = mk<AND>(replaceInSubexpr(body, s, s->right(), var_it), mk<EQ>(s->right(), var_it));
      }
    }
  }

  inline static bool isSymmetric (Expr exp)
  {
    return isOpX<EQ>(exp);
  }

  // very naive version, to extend
  inline ExprSet orifyCmpConstraintsSet(ExprSet& es, int bnd = 10)
  {
    assert (es.size() > 0);
    if (es.size() == 1)
    {
      ExprSet newDsjs;
      getDisj(*es.begin(), newDsjs);
      return newDsjs;
    }

    bool toDisj;
    ExprFactory &efac = (*es.begin())->getFactory();
    Expr lhs;
    int lowerBnd = INT_MIN;
    int upperBnd = INT_MAX;
    for (auto & a : es)
    {
      toDisj = false;
      if (!isOp<ComparissonOp>(a)) break;
      if (isOpX<EQ>(a))
      {
        ExprSet newDsjs;
        newDsjs.insert(a);
        return newDsjs;
      }

      if (lhs == NULL) lhs = a->left();
      else
        if (0 != lexical_cast<string>(lhs).compare(lexical_cast<string>(a->left()))) break;

      if (!isOpX<MPZ>(a->right())) break;

      if (isOpX<GEQ>(a)) lowerBnd = max(lowerBnd, lexical_cast<int>(a->right()));
      else if (isOpX<GT>(a)) lowerBnd = max(lowerBnd, lexical_cast<int>(a->right()) + 1);
      else if (isOpX<LEQ>(a)) upperBnd = min(upperBnd, lexical_cast<int>(a->right()));
      else if (isOpX<LT>(a)) upperBnd = min(upperBnd, lexical_cast<int>(a->right()) - 1);

      toDisj = true;
    }

    ExprSet newDsjs;
    if (toDisj)
    {
      for (int i = 0; i < min(bnd, upperBnd - lowerBnd); i++)
      {
        newDsjs.insert(mk<EQ>(lhs, mkTerm (mpz_class (lowerBnd + i), efac)));
      }
      if (upperBnd - lowerBnd > bnd)
      {
        newDsjs.insert(mk<AND>
                (mk<GEQ>(lhs, mkTerm (mpz_class (lowerBnd + bnd), efac)),
                 mk<LEQ>(lhs, mkTerm (mpz_class (upperBnd), efac))));
      }
    }
    else
    {
      newDsjs.insert(conjoin(es, efac));
    }
    return newDsjs;
  }

  inline void getNondets (Expr e, std::map<Expr, ExprSet>& nondets)
  {
    ExprSet lin;
    getConj(e, lin);
    std::map<Expr, ExprSet> constraints;
    for (auto & a : lin)
    {
      if (isOpX<GT>(a) || isOpX<LT>(a) || isOpX<GEQ>(a) || isOpX<LEQ>(a) || isOpX<ITE>(a) || isOpX<OR>(a))
      {
        ExprVector av;
        filter (a, bind::IsConst (), inserter(av, av.begin()));
        if (av.size() == 0 || av.size() > 1) continue;
        // current limitation: only nondeterminism w.r.t. one variable; to extend

        Expr a1 = (unfoldITE(a));
        a1 = simplifyBool(a1);
        getConj(a1, constraints[*av.begin()]);
      }
    }

    for (auto & a : constraints){
      nondets[a.first] = orifyCmpConstraintsSet(a.second);
    }
  }

  Expr processNestedStores (Expr exp, ExprSet& cnjs)
  {
    // TODO: double check if cells are overwritten
    Expr arrVar = exp->left();
    if (isOpX<STORE>(arrVar)) arrVar = processNestedStores(arrVar, cnjs);
    Expr indVar = exp->right();
    Expr valVar = exp->last();
    cnjs.insert(mk<EQ>(mk<SELECT>(arrVar, indVar), valVar));
    return arrVar;
  }

  struct TransitionOverapprox
  {
    ExprVector& srcVars;
    ExprVector& dstVars;

    TransitionOverapprox (ExprVector& _srcVars, ExprVector& _dstVars):
      srcVars(_srcVars), dstVars(_dstVars) {};

    Expr operator() (Expr exp)
    {
      if (isOp<ComparissonOp>(exp) && !containsOp<ITE>(exp))
      {
        ExprSet tmp;
        if (isOpX<STORE>(exp->left()))
        {
          processNestedStores(exp->left(), tmp);
          return conjoin(tmp, exp->getFactory());
        }
        else if (isOpX<STORE>(exp->right()))
        {
          processNestedStores(exp->right(), tmp);
          return conjoin(tmp, exp->getFactory());
        }

        ExprVector av;
        filter (exp, bind::IsConst (), inserter(av, av.begin()));
        if (!emptyIntersect(av, srcVars) && !emptyIntersect(av, dstVars))
          return mk<TRUE>(exp->getFactory());
      }
      else if (isOpX<OR>(exp))
      {
        ExprSet newDsjs;
        for (unsigned i = 0; i < exp->arity (); i++)
        {
          ExprSet cnjs;
          getConj(exp->arg(i), cnjs);
          map<Expr, bool> sels;
          bool allselects = true;
          bool noselects = true;
          for (auto & a : cnjs)
          {
            sels[a] = containsOp<SELECT>(a);
            if (sels[a]) noselects = false;
            else allselects = false;
          }
          if (!noselects && ! allselects)
          {
            ExprSet newCnjs;
            for (auto & a : cnjs)
              if (sels[a]) newCnjs.insert(a);
            newDsjs.insert(conjoin(newCnjs,exp->getFactory()));
          }
        }
        return disjoin(newDsjs,exp->getFactory());
      }
      return exp;
    }
  };

  // opposite to TransitionOverapprox
  struct TransitionMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprVector& srcVars;
    ExprVector& dstVars;
    ExprSet& transitions;

    TransitionMiner (ExprVector& _srcVars, ExprVector& _dstVars, ExprSet& _transitions):
      srcVars(_srcVars), dstVars(_dstVars), transitions(_transitions) {};

    VisitAction operator() (Expr exp)
    {
      if (isOp<ComparissonOp>(exp) && !containsOp<ITE>(exp))
      {
        ExprVector av;
        filter (exp, bind::IsConst (), inserter(av, av.begin()));
        if (!emptyIntersect(av, srcVars) && !emptyIntersect(av, dstVars))
        {
          transitions.insert(exp);
        }
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  struct BoolEqRewriter
  {
    BoolEqRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        if (bind::isBoolConst(lhs) || bind::isBoolConst(rhs) ||
            isOpX<NEG>(lhs) || isOpX<NEG>(rhs))
        {
          return mk<AND>(mk<OR>(mkNeg(lhs), rhs),
                         mk<OR>(lhs, mkNeg(rhs)));
        }
        return exp;
      }
      return exp;
    }
  };

  struct CondRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& conds;

    CondRetriever (ExprSet& _conds) :  conds(_conds) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<ITE>(exp))
      {
        conds.insert(exp->arg(0));
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  struct AccessRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& accs;

    AccessRetriever (ExprSet& _accs) :  accs(_accs) {};

    VisitAction operator() (Expr exp)
    {
      if ((isOpX<SELECT>(exp) || isOpX<STORE>(exp)) && !findArray(exp->right()))
      {
        accs.insert(exp->right());
      }
      return VisitAction::doKids ();
    }
  };

  struct DeltaRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprVector& srcVars;
    ExprVector& dstVars;
    ExprSet& deltas;

    DeltaRetriever (ExprVector& _srcVars, ExprVector& _dstVars, ExprSet& _deltas):
    srcVars(_srcVars), dstVars(_dstVars), deltas(_deltas) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        ExprVector av;
        filter (exp, bind::IsConst (), inserter(av, av.begin()));
        if (av.size() != 2) return VisitAction::skipKids ();;
        for (int i = 0; i < srcVars.size(); i++)
        {
          if ((av[0] == srcVars[i] && av[1] == dstVars[i]) ||
              (av[1] == srcVars[i] && av[0] == dstVars[i]))
          {
            set<int> coefs;
            exp = normalizeAtom(exp, av);
            if (!getLinCombCoefs(exp, coefs)) continue;

            bool success = true;
            for (auto i : coefs) success = success && (i == -1 || i == 1);
            if (success)
            {
              Expr cExpr = exp->right();
              int c = abs(lexical_cast<int>(cExpr));
              if (c > 1)
              {
                Expr cand = mk<GEQ>(mk<MOD>(srcVars[i],
                                        mkTerm (mpz_class (c), exp->getFactory())),
                                        mkTerm (mpz_class (0), exp->getFactory()));
                deltas.insert(cand);
              }
            }
          }
        }
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline Expr rewriteBoolEq (Expr exp)
  {
    RW<BoolEqRewriter> tr(new BoolEqRewriter());
    return dagVisit (tr, exp);
  }

  inline void retrieveDeltas (Expr exp, ExprVector& srcVars, ExprVector& dstVars, ExprSet& deltas)
  {
    DeltaRetriever dr (srcVars, dstVars, deltas);
    dagVisit (dr, exp);
  }

  inline void retrieveConds (Expr exp, ExprSet& conds)
  {
    CondRetriever dr (conds);
    dagVisit (dr, exp);
  }

  inline void retrieveAccFuns (Expr exp, ExprSet& accs)
  {
    AccessRetriever dr (accs);
    dagVisit (dr, exp);
  }

  inline void retrieveTransitions (Expr exp, ExprVector& srcVars, ExprVector& dstVars, ExprSet& transitions)
  {
    TransitionMiner trm (srcVars, dstVars, transitions);
    dagVisit (trm, exp);
  }

  inline static Expr overapproxTransitions (Expr exp, ExprVector& srcVars, ExprVector& dstVars)
  {
    RW<TransitionOverapprox> rw(new TransitionOverapprox(srcVars, dstVars));
    return dagVisit (rw, exp);
  }

  inline static Expr mergeIneqs (Expr e1, Expr e2)
  {
    if (isOpX<NEG>(e1)) e1 = mkNeg(e1->last());
    if (isOpX<NEG>(e2)) e2 = mkNeg(e2->last());

    if (isOpX<GEQ>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->left())
      return mk<GEQ>(e1->left(), e2->right());
    if (isOpX<GT>(e1) && isOpX<GT>(e2) && e1->right() == e2->left())
      return mk<GT>(e1->left(), e2->right());
    if (isOpX<GEQ>(e1) && isOpX<GT>(e2) && e1->right() == e2->left())
      return mk<GT>(e1->left(), e2->right());
    if (isOpX<GT>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->left())
      return mk<GT>(e1->left(), e2->right());
    if (isOpX<GT>(e1) && isOpX<GEQ>(e2) && (e1->left() == e2->right()))
      return mk<GT>(e2->left(), e1->right());

    if (isOpX<LEQ>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->left())
      return mk<LEQ>(e1->left(), e2->right());
    if (isOpX<LT>(e1) && isOpX<LT>(e2) && e1->right() == e2->left())
      return mk<LT>(e1->left(), e2->right());
    if (isOpX<LEQ>(e1) && isOpX<LT>(e2) && e1->right() == e2->left())
      return mk<LT>(e1->left(), e2->right());
    if (isOpX<LT>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->left())
      return mk<LT>(e1->left(), e2->right());

    if (isOpX<LEQ>(e1) && isOpX<LEQ>(e2) && e2->right() == e1->left())
      return mk<LEQ>(e2->left(), e1->right());
    if (isOpX<LT>(e2) && isOpX<LT>(e1) && e2->right() == e1->left())
      return mk<LT>(e2->left(), e1->right());
    if (isOpX<LEQ>(e2) && isOpX<LT>(e1) && e2->right() == e1->left())
      return mk<LT>(e2->left(), e1->right());
    if (isOpX<LT>(e2) && isOpX<LEQ>(e1) && e2->right() == e1->left())
      return mk<LT>(e2->left(), e1->right());

    if (isOpX<LEQ>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->right())
      return mk<LEQ>(e1->left(), e2->left());
    if (isOpX<LT>(e1) && isOpX<GT>(e2) && e1->right() == e2->right())
      return mk<LT>(e1->left(), e2->left());
    if (isOpX<LEQ>(e1) && isOpX<GT>(e2) && e1->right() == e2->right())
      return mk<LT>(e1->left(), e2->left());
    if (isOpX<LT>(e1) && isOpX<GEQ>(e2) && e1->right() == e2->right())
      return mk<LT>(e1->left(), e2->left());

    if (isOpX<LEQ>(e1) && isOpX<GEQ>(e2) && e1->left() == e2->left())
      return mk<LEQ>(e2->right(), e1->right());
    if (isOpX<LT>(e1) && isOpX<GT>(e2) && e1->left() == e2->left())
      return mk<LT>(e2->right(), e1->right());
    if (isOpX<LEQ>(e1) && isOpX<GT>(e2) && e1->left() == e2->left())
      return mk<LT>(e2->right(), e1->right());
    if (isOpX<LT>(e1) && isOpX<GEQ>(e2) && e1->left() == e2->left())
      return mk<LT>(e2->right(), e1->right());

    if (isOpX<GEQ>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->right())
      return mk<GEQ>(e1->left(), e2->left());
    if (isOpX<GT>(e1) && isOpX<LT>(e2) && e1->right() == e2->right())
      return mk<GT>(e1->left(), e2->left());
    if (isOpX<GEQ>(e1) && isOpX<LT>(e2) && e1->right() == e2->right())
      return mk<GT>(e1->left(), e2->left());
    if (isOpX<GT>(e1) && isOpX<LEQ>(e2) && e1->right() == e2->right())
      return mk<GT>(e1->left(), e2->left());

    // TODO: support more cases
    return NULL;
  }

  inline static Expr mergeIneqsWithVar (Expr e, Expr var)
  {
    ExprSet cnjs;
    ExprVector cnjs2;
    ExprSet cnjs3;
    getConj(e, cnjs);
    for (auto & a : cnjs)
      if (contains(a, var)) cnjs2.push_back(a);
      else cnjs3.insert(a);

    if (cnjs2.size() != 2) return e;

    if(mergeIneqs(cnjs2[0], cnjs2[1]) == NULL) return NULL;

    cnjs3.insert(mergeIneqs(cnjs2[0], cnjs2[1]));
    return conjoin(cnjs3, e->getFactory());
  }

  template <typename T> static void computeTransitiveClosure(ExprSet& r, ExprSet& tr)
  {
    for (auto &a : r)
    {
      if (isOpX<T>(a))
      {
        for (auto &b : tr)
        {
          if (isOpX<T>(b))
          {
            if (a->left() == b->right()) tr.insert(mk<T>(b->left(), a->right()));
            if (b->left() == a->right()) tr.insert(mk<T>(a->left(), b->right()));
            
            if (isSymmetric(a))
            {
              if (a->left()  == b->left())  tr.insert(mk<T>(a->right(), b->right()));
              if (a->right() == b->right()) tr.insert(mk<T>(a->left(),  b->left()));
            }
          }
        }
      }
      tr.insert(a);
    }
  }

  struct TransClAdder
  {
    TransClAdder () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet trCnjs;
        getConj(exp, cnjs);
        computeTransitiveClosure<EQ>(cnjs, trCnjs);
        computeTransitiveClosure<LEQ>(cnjs, trCnjs);
        computeTransitiveClosure<GEQ>(cnjs, trCnjs);
        computeTransitiveClosure<LT>(cnjs, trCnjs);
        computeTransitiveClosure<GT>(cnjs, trCnjs);
        return conjoin(trCnjs, exp->getFactory());
      }

      return exp;
    }
  };
  
  inline static Expr enhanceWithMoreClauses (Expr exp)
  {
    RW<TransClAdder> tr(new TransClAdder());
    return dagVisit (tr, exp);
  }
  
  inline static Expr propagateEqualities (Expr exp)
  {
    ExprSet cnjs;
    ExprSet eqs;
    ExprSet trEqs;
    
    getConj(exp, cnjs);
    
    for (auto &a : cnjs) if (isOpX<EQ>(a)) eqs.insert(a);
    if (eqs.size() == 0) return exp;
    
    computeTransitiveClosure<EQ>(eqs, trEqs);
    
    for (auto &a : trEqs)
    {
      if (isOpX<EQ>(a))
      {
        bool toAdd = true;
        for (auto & c : cnjs)
        {
          if (isOpX<EQ>(c))
          {
            if (c->left() == a->left() && c->right() == a->right()) { toAdd = false; break; }
            if (c->left() == a->right() && c->right() == a->left()) { toAdd = false; break; }
          }
        }
        if (toAdd) cnjs.insert(a);
      }
// TODO: double-check if it is needed:
/*      else
      {
        Expr neg = mkNeg(a);
        for (auto &b : trEqs)
        {
          Expr repl1 = replaceAll(neg, b->left(), b->right());
          Expr repl2 = replaceAll(neg, b->right(), b->left());
          bool eq1 = (repl1 == neg);
          bool eq2 = (repl2 == neg);
          bool eq3 = (repl2 == repl1);
          
          if (eq1 && eq2 && eq3) cnjs.insert(a);
          else if (eq1) cnjs.insert (mk<NEG> (mk<AND>(neg, repl2)));
          else if (eq2) cnjs.insert (mk<NEG> (mk<AND>(neg, repl1)));
          else cnjs.insert(mk<NEG> (mk<AND>(neg, mk<AND>(repl1, repl2))));
        }
      } */
    }
    
    return conjoin(cnjs, exp->getFactory());
  }

  bool isConstExpr(Expr e) {
    using namespace expr::op::bind;
    if (isIntConst(e) || isBoolConst(e) || isRealConst(e)) return true;
    return false;
  }

  bool isLitExpr(Expr e) {
    int arity = e->arity();
    if (isConstExpr(e)) return false;
    if (arity == 0) return true;
    bool res = true;
    for (int i = 0; i < arity; i++) {
      res = res && isLitExpr(e->arg(i));
    }
    return res;
  }

  bool isConstAddModExpr(Expr e) {
    using namespace expr::op::bind;
    if (isOp<PLUS>(e) || isOp<MINUS>(e) || isOp<MOD>(e)) {
      if (isLitExpr(e->arg(0))) {
        return isConstAddModExpr(e->arg(1));
      }
      if (isLitExpr(e->arg(1))) {
        return isConstAddModExpr(e->arg(0));
      }
    }
    return isConstExpr(e);
  }

  bool isNonlinear(Expr e) {
    if (isOpX<BVSORT>(e)) return true;
    int arity = e->arity();
    if (isOp<MOD>(e)) {
      if (isLitExpr(e->arg(0))) {
        return !(isLitExpr(e->arg(1)) || !isConstExpr(e->arg(1)));
      }
      if (isLitExpr(e->arg(1))) {
        return !(isConstAddModExpr(e->arg(0)));
      }
      return true;
    }
    if (isOp<MULT>(e) || isOp<DIV>(e)) {
      if (isLitExpr(e->arg(0))) {
        return isNonlinear(e->arg(1));
      }
      if (isLitExpr(e->arg(1))) {
        return isNonlinear(e->arg(0));
      }
      return true;
    }
    bool res = false;
    for (int i = 0; i < arity; i++) {
      res = res || isNonlinear(e->arg(i));
    }
    return res;
  }

  inline static bool evalLeq(Expr a, Expr b)
  {
    if (isOpX<MPZ>(a) && isOpX<MPZ>(b)) {
      return getTerm<mpz_class>(a) <= getTerm<mpz_class>(b);
    }
    else return (a == b); // GF: to extend
  }

  inline static void mutateHeuristic (Expr exp, ExprSet& guesses /*, int bnd = 100*/)
  {
    exp = unfoldITE(exp);
    ExprSet cnjs;
    getConj(exp, cnjs);
    ExprSet ineqs;
    ExprSet eqs;
    ExprSet disjs;
    for (auto c : cnjs)
    {
      if (isOpX<NEG>(c)) c = mkNeg(c->left());

      if (isOpX<EQ>(c))
      {
        if (isNumeric(c->left()))
        {
          eqs.insert(c);
          ineqs.insert(mk<LEQ>(c->right(), c->left()));
          ineqs.insert(mk<LEQ>(c->left(), c->right()));
        }
        else
        {
          guesses.insert(c);
        }
      }
      else if (isOp<ComparissonOp>(c))
      {
        if (isOpX<LEQ>(c)) ineqs.insert(c);
        else if (isOpX<GEQ>(c)) ineqs.insert(mk<LEQ>(c->right(), c->left()));
        else if (isOpX<GT>(c))
        {
          if (isOpX<MPZ>(c->left()))
            ineqs.insert(mk<LEQ>(c->right(), mkTerm (mpz_class (lexical_cast<int>(c->left())-1), exp->getFactory())));
          else if(isOpX<MPZ>(c->right()))
            ineqs.insert(mk<LEQ>(mkTerm (mpz_class (lexical_cast<int>(c->right())+1), exp->getFactory()), c->left()));
          else
            ineqs.insert(mk<LEQ>(c->right(), mk<MINUS>(c->left(), mkTerm (mpz_class (1), exp->getFactory()))));
        }
        else if (isOpX<LT>(c))
        {
          if (isOpX<MPZ>(c->left()))
            ineqs.insert(mk<LEQ>(mkTerm (mpz_class (lexical_cast<int>(c->left())+1), exp->getFactory()), c->right()));
          else if(isOpX<MPZ>(c->right()))
            ineqs.insert(mk<LEQ>(c->left(), mkTerm (mpz_class (lexical_cast<int>(c->right())-1), exp->getFactory())));
          else
            ineqs.insert(mk<LEQ>(c->left(), mk<MINUS>(c->right(), mkTerm (mpz_class (1), exp->getFactory()))));
        }
        else
        {
          assert (isOpX<NEQ>(c));
          guesses.insert(c);
        }
      }
      else if (isOpX<OR>(c))
      {
        ExprSet terms;
        getDisj(c, terms);
        ExprSet newTerms;
        for (auto t : terms)
        {
          if (newTerms.size() > 2) continue; // don't consider large disjunctions
          if (isOpX<NEG>(t)) t = mkNeg(t->left());
          if (!isOp<ComparissonOp>(t)) continue;
          if (!isNumeric(t->left())) continue;
          newTerms.insert(t);
        }
        c = disjoin(newTerms, c->getFactory());
        disjs.insert(c);
        guesses.insert(c);
      }
      else guesses.insert(c);
    }


    ExprSet newIneqs;
    for (auto & z : eqs)
    {
      for (auto & in : ineqs)
      {
        //if (bnd > guesses.size()) return;
        if (!emptyIntersect(z, in)) continue;
        newIneqs.insert(mk<LEQ>(mk<PLUS>(in->left(), z->left()), mk<PLUS>(in->right(), z->right())));
        newIneqs.insert(mk<LEQ>(mk<PLUS>(in->left(), z->right()), mk<PLUS>(in->right(), z->left())));
      }

      for (auto & d : disjs)
      {
        //if (bnd > guesses.size()) return;
        ExprSet terms;
        getDisj(d, terms);
        ExprSet newTerms;
        for (auto c : terms)
        {
          if (isOp<ComparissonOp>(c))
          {
            if (emptyIntersect(z, c))
              newTerms.insert(reBuildCmp(c,
                mk<PLUS>(c->left(), z->left()), mk<PLUS>(c->right(), z->right())));
            else newTerms.insert(c);
          }
          else newTerms.insert(c);
        }
        if (newTerms.size() > 0)
          guesses.insert(disjoin(newTerms, d->getFactory()));
      }
    }

    ineqs.insert(newIneqs.begin(), newIneqs.end());
    newIneqs.clear();
    guesses.insert(ineqs.begin(), ineqs.end());

    for (auto & e : eqs)
    {
      for (auto & in : ineqs)
      {
        //if (bnd > guesses.size()) return;
        assert(isOpX<LEQ>(in));
        Expr g;
        if (in->left() == e->left() && !evalLeq(e->right(), in->right()))
          g = mk<LEQ>(e->right(), in->right());
        else if (in->left() == e->right() && !evalLeq(e->left(), in->right()))
          g = mk<LEQ>(e->left(), in->right());
        else if (in->right() == e->left() && !evalLeq(in->left(), e->right()))
          g = mk<LEQ>(in->left(), e->right());
        else if (in->right() == e->right() && !evalLeq(in->left(), e->left()))
          g = mk<LEQ>(in->left(), e->left());

        if (g != NULL) guesses.insert(g);
      }
    }

    for (auto & in1 : ineqs)
    {
      for (auto & in2 : ineqs)
      {
//        if (bnd > guesses.size()) return;
        if (in1 == in2) continue;

        assert(isOpX<LEQ>(in1));
        assert(isOpX<LEQ>(in2));

        if (evalLeq(in1->right(), in2->left()) &&
            !evalLeq(in1->left(), in2->right()))
        {
          guesses.insert(mk<LEQ>(in1->left(), in2->right()));
        }
      }
    }
  }


  inline static void mutateHeuristicBV (Expr exp, ExprSet& guesses /*, int bnd = 100*/)
  {
//    std::cout << "Mutate called on " << *exp << std::endl;
    exp = unfoldITE(exp);
    ExprSet cnjs;
    getConj(exp, cnjs);
    ExprSet ineqs;
    ExprSet eqs;
    ExprSet disjs;
    for (auto c : cnjs)
    {
      if (isOpX<NEG>(c)) c = c->left();

      if (isOpX<EQ>(c))
      {
        if (isNumeric(c->left()))
        {
          eqs.insert(c);
          ineqs.insert(bv::bvule(c->right(), c->left()));
          ineqs.insert(bv::bvule(c->left(), c->right()));
          // TODO: signed?
        }
        else
        {
          guesses.insert(c);
        }
      }
      else if (bv::isBVComparison(c))
      {
        c = convertBVToLeqAndLt(c);
        guesses.insert(c);
        ineqs.insert(c);
      }
      else if (isOpX<OR>(c))
      {
        ExprSet terms;
        getDisj(c, terms);
        ExprSet newTerms;
        for (auto t : terms)
        {
          if (newTerms.size() > 2) continue; // don't consider large disjunctions
          if (isOpX<NEG>(t)) t = mkNeg(t->left());
          if (!bv::isBVComparison(t)) continue;
          if (!isNumeric(t->left())) continue;
          newTerms.insert(t);
        }
        c = disjoin(newTerms, c->getFactory());
        disjs.insert(c);
        guesses.insert(c);
      }
      else guesses.insert(c);
    }

    for (auto & z : eqs)
    {
      for (auto & in : ineqs)
      {
        //if (bnd > guesses.size()) return;
        if (!emptyIntersect(z, in)) continue;
        ineqs.insert(bv::bvule(bv::bvadd(in->left(), z->left()),bv::bvadd(in->right(), z->right())));
        ineqs.insert(bv::bvule(bv::bvadd(in->left(), z->right()),bv::bvadd(in->right(), z->left())));
      }

      for (auto & d : disjs)
      {
        //if (bnd > guesses.size()) return;
        ExprSet terms;
        getDisj(d, terms);
        ExprSet newTerms;
        for (auto c : terms)
        {
          if (bv::isBVComparison(c))
          {
            if (emptyIntersect(z, c))
              newTerms.insert(reBuildCmp(c,
                                         bv::bvadd(c->left(), z->left()), bv::bvadd(c->right(), z->right())));
            else newTerms.insert(c);
          }
          else newTerms.insert(c);
        }
        if (newTerms.size() > 0)
          guesses.insert(disjoin(newTerms, d->getFactory()));
      }
    }

    guesses.insert(ineqs.begin(), ineqs.end());

    for (auto & e : eqs)
    {
      for (auto & in : ineqs)
      {
        //if (bnd > guesses.size()) return;
//        assert(isOpX<LEQ>(in));
        Expr g;
        if (in->left() == e->left() && !evalLeq(e->right(), in->right()))
          g = reBuildCmp(in, e->right(), in->right());
        else if (in->left() == e->right() && !evalLeq(e->left(), in->right()))
          g = reBuildCmp(in, e->left(), in->right());
        else if (in->right() == e->left() && !evalLeq(in->left(), e->right()))
          g = reBuildCmp(in, in->left(), e->right());
        else if (in->right() == e->right() && !evalLeq(in->left(), e->left()))
          g = reBuildCmp(in, in->left(), e->left());

        if (g != NULL) guesses.insert(g);
      }
    }

    for (auto & in1 : ineqs)
    {
      for (auto & in2 : ineqs)
      {
  //        if (bnd > guesses.size()) return;
        if (in1 == in2) continue;

        if (isOpX<BULE>(in1) && isOpX<BULE>(in2) && (in1->right() == in2->left())) {
          guesses.insert(bv::bvule(in1->left(), in2->right()));
        }
      }
    }
  }
}

#endif
