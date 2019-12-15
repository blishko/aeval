//
// Created by Martin Blicha on 31.10.19.
//

#ifndef SEAHORN_EXPRTRANSLATIONS_H
#define SEAHORN_EXPRTRANSLATIONS_H

#include "Expr.hpp"

namespace expr {
  namespace op {
    namespace bv {

      mpz_class power(unsigned long base, unsigned long exp) {
        mpz_class res;
        mpz_ui_pow_ui(res.get_mpz_t(), base, exp);
        return res;
      }

      mpz_class getUpperBoundForBitWidth(long width) {
        return power(2, width);
      }

      Expr getUpperBoundForBitWidthExpr(long width, ExprFactory& fact) {
        return mkTerm(getUpperBoundForBitWidth(width), fact);
      }

      class BV2LIATranslator
      {
      public:
        using subs_t = std::map<Expr, Expr>;
        using bits_t = std::map<Expr, int>;
        BV2LIATranslator(subs_t const & subs, subs_t const & decls, bits_t const & bits) :
        varMap{subs}, declsMap{decls}, bitwidths{bits}
        {}

        Expr operator()(Expr e);
        subs_t getAbstractionsMap() const { return abstractionsMap; }

      private:
        Expr _bv2lia(Expr e);

        const subs_t& varMap;
        const subs_t& declsMap;
        const bits_t& bitwidths;
        subs_t abstractionsMap;
        std::size_t freshCounter = 0;
        std::string getFreshName() {
          return std::string("BV2LIA_abs_") + std::to_string(freshCounter++);
        }

        Expr getOrCreateAbstractionVariableFor(Expr e) {
          auto it = abstractionsMap.find(e);
          if (it != abstractionsMap.end()) { return it->second; }
          Expr fresh = bind::intConst(mkTerm<std::string>(getFreshName(), e->getFactory()));
          abstractionsMap.insert(std::make_pair(e, fresh));
          return fresh;
        }
      };

      class BV2LIAVisitor {
        BV2LIATranslator* translator;
      public:
        void setTranslator(BV2LIATranslator * trans) { this->translator = trans; }
        VisitAction operator()(Expr e) {
          if (e->arity() == 0)
            return VisitAction::skipKids ();
          if (!translator) { throw std::logic_error("No translator set!"); }
          BV2LIATranslator& trans = *translator;
          Expr tr = trans(e);
          return VisitAction::changeDoKids(tr);
        }
      };

      Expr BV2LIATranslator::operator()(Expr e) {
        return this->_bv2lia(e);
      }

      Expr BV2LIATranslator::_bv2lia(Expr e) {
//        std::cout << e << std::endl;
//        {
//          auto it = abstractionsMap.find(e);
//          if (it != abstractionsMap.end()) { return it->second; }
//        }
        if (isOpX<AND>(e) || isOpX<OR>(e) || isOpX<NEG>(e) || isOpX<EQ>(e) || isOpX<NEQ>(e) || isOpX<ITE>(e)
            || bind::isBoolConst(e) || bind::isIntConst(e)
          )
        {
          return e;
        }
        if (op::bv::is_bvnum(e)) {
          Expr val = e->arg(0);
          return val;
        }
        if (is_bvconst(e) || is_bvvar(e)) {
          if (varMap.find(e) == varMap.end()) {
            std::cerr << "Missing variable in varMap: " << e << std::endl;
              assert(false);
          }
          return varMap.at(e);
        }
        if (isOpX<FAPP>(e)) {
          // MB: Probably nothing to do
          return e;
        }
        if (isOpX<BADD>(e)) {
          auto wit = bitwidths.find(e);
          assert(wit != bitwidths.end());
          int width = wit->second;
          Expr bound = getUpperBoundForBitWidthExpr(width, e->getFactory());
          Expr plus = mk<PLUS>(e->left(), e->right());
          return mk<ITE>(mk<GEQ>(plus, bound), mk<MINUS>(plus, bound), plus);
        }
        if (isOpX<BSUB>(e)) {
          Expr minus = mk<MINUS>(e->left(), e->right());
          auto wit = bitwidths.find(e);
          assert(wit != bitwidths.end());
          int width = wit->second;
          Expr bound = getUpperBoundForBitWidthExpr(width, e->getFactory());
          return mk<ITE>(mk<LT>(minus, mkTerm(mpz_class(0), e->getFactory())), mk<PLUS>(minus, bound), minus);
        }
        if (isOpX<BMUL>(e)) {
          assert(e->arity() == 2);
          Expr left = e->left();
          Expr right = e->right();
          bool hasConstant = bv::is_bvnum(left) || bv::is_bvnum(right);
          if (hasConstant) {
            return mk<MULT>(left, right);
          }
         // We need to abstract away
         return getOrCreateAbstractionVariableFor(e);
        }
        if (isOpX<BUREM>(e)) {
          assert(e->arity() == 2);
          Expr left = e->left();
          Expr right = e->right();
          bool isRightConst = bv::is_bvnum(right);
          if (isRightConst) {
            return mk<DIV>(left, right);
          }
          // We need to abstract away
          return getOrCreateAbstractionVariableFor(e);
        }
        if (isOpX<BNEG>(e)) {
          assert(e->arity() == 1);
          // Unary minus through 2's complement
          Expr arg = e->first();
          auto width = bitwidths.at(arg);
          Expr bound = getUpperBoundForBitWidthExpr(width, e->getFactory());
          return mk<MINUS>(bound, arg);
        }
        if (isOpX<BSHL>(e)) {
          assert(e->arity() == 2);
          Expr left = e->left();
          Expr right = e->right();
          bool isShiftByConst = bv::is_bvnum(right);
          if (isShiftByConst) {
            mpz_class exp = getTerm<mpz_class>(right->first());
            if (mpz_fits_uint_p(exp.get_mpz_t()) == 0) { goto fallbacklsh; }
            auto exp_small = exp.get_ui();
            if (exp_small >= bitwidths.at(left)) { goto fallbacklsh; }
            // It is shift by a sufficiently small number, we can represent this as multiplication
            mpz_class val = power(2, exp_small);
            // ITE to take overflow into accout
            Expr mult = mk<MULT>(left, mkTerm(val, e->getFactory()));
            int width = bitwidths.at(left);
            Expr upperBound = getUpperBoundForBitWidthExpr(width, e->getFactory());
            // abstraction
            Expr var = getOrCreateAbstractionVariableFor(mult);
            return mk<ITE>(mk<GEQ>(mult, upperBound), var, mult);
          }
          fallbacklsh:
          // Just abstract the whole epression away
          return getOrCreateAbstractionVariableFor(e);
        }
        if (isOpX<BLSHR>(e)) {
          assert(e->arity() == 2);
          Expr left = e->left();
          Expr right = e->right();
          bool isShiftByConst = bv::is_bvnum(right);
          if (isShiftByConst) {
            mpz_class exp = getTerm<mpz_class>(right->first());
            if (mpz_fits_uint_p(exp.get_mpz_t()) == 0) { goto fallbacklshr; }
            auto exp_small = exp.get_ui();
            if (exp_small >= bitwidths.at(left)) { goto fallbacklshr; }
            // It is shift by a sufficiently small number, we can represent this as multiplication
            mpz_class val = power(2, exp_small);
            // ITE to take overflow into accout
            Expr divExpr = mk<DIV>(left, mkTerm(val, e->getFactory()));
            return divExpr;
          }
          fallbacklshr:
          // Just abstract the whole epression away
          return getOrCreateAbstractionVariableFor(e);
        }
        if (isOpX<BUGE>(e)) {
          return mk<GEQ>(e->left(), e->right());
        }
        if (isOpX<BUGT>(e)) {
          return mk<GT>(e->left(), e->right());
        }
        if (isOpX<BULE>(e)) {
          return mk<LEQ>(e->left(), e->right());
        }
        if (isOpX<BULT>(e)) {
          return mk<LT>(e->left(), e->right());
        }
        if (isOpX<BAND>(e) || isOpX<BOR>(e) || isOpX<BXOR>(e)) {
          // MB: abstract for now
          return getOrCreateAbstractionVariableFor(e);
        }
        if (isOpX<BEXTRACT>(e)) {
          auto it = bitwidths.find(bv::earg(e));
          assert(it != bitwidths.end());
          int width = it->second;
          int low = bv::low(e);
          int high = bv::high(e);
          if (high + 1 == width) {
            // Extracting some upper part of bits, we can use div
            mpz_class divArg = power(2, low);
            auto divArgExpr = mkTerm(divArg, e->getFactory());
            return mk<DIV>(bv::earg(e), divArgExpr);
          }
          if (low == 0 && high == 0) {
            return mk<MOD>(e->arg(2), mkTerm(mpz_class(2), e->getFactory()));
          }
          // For now, introduce a fresh variable for this expression
//          std::cout << "Warning! Abstracting away bvextract expression " << *e << std::endl;
          Expr var = bv::high(e) == bv::low(e) ?
            bind::boolConst(mkTerm<std::string>(getFreshName(), e->getFactory()))
            : bind::intConst(mkTerm<std::string>(getFreshName(), e->getFactory()));
          abstractionsMap[e] = var;
          return var;
        }
        if (isOpX<BCONCAT>(e)) {
          Expr arg1 = e->first();
          if (bv::is_bvnum(arg1)) {
            Expr val = arg1->first();
            auto mpzVal = getTerm<mpz_class>(val);
            assert(bind::IsHardIntConst{}(val));
            if (mpzVal == 0) {
              return _bv2lia(e->arg(1));
            }
            Expr arg2 = e->arg(1);
            auto it = bitwidths.find(arg2);
            assert(it != bitwidths.end());
            mpz_class shift = power(2, it->second);
            mpz_class plusMpz = shift * mpzVal;
            return mk<PLUS>(arg2, mkTerm(plusMpz, e->getFactory()));
          }
          // For now, abstract away with a fresh variable
//          std::cout << "Warning! Abstracting away bvconcat expression " << *e << std::endl;
          return getOrCreateAbstractionVariableFor(e);
        }
        if (isOp<FDECL>(e)) {
          auto iter = declsMap.find(e);
          if (iter != declsMap.end()) { return iter->second; }
          // MB: otherwise nothing to do
          return e;
        }
        if (isOp<ComparissonOp>(e) || isOp<NumericOp>(e)) {
          return e;
        }
        // MB: add cases if necessary
        std::cerr << "Case not covered yet: " << e << std::endl;
        throw std::logic_error("Expression not covered in translation from BV to LIA!" + std::string(__FILE__) + "line " + std::to_string(__LINE__));
        return e;
      }
    }
  }
}

#endif //SEAHORN_EXPRTRANSLATIONS_H
