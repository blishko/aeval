//
// Created by Martin Blicha on 31.10.19.
//

#ifndef SEAHORN_EXPRTRANSLATIONS_H
#define SEAHORN_EXPRTRANSLATIONS_H

#include "Expr.hpp"

namespace expr {
  namespace op {
    namespace bv {

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
        auto it = abstractionsMap.find(e);
        if (it != abstractionsMap.end()) { return it->second; }
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
          assert(varMap.find(e) != varMap.end());
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
          mpz_class upperBound;
          mpz_ui_pow_ui(upperBound.get_mpz_t(), 2, width);
          Expr plus = mk<PLUS>(e->left(), e->right());
          Expr bound = mkTerm(upperBound, e->getFactory());
          return mk<ITE>(mk<GEQ>(plus, bound), mk<MINUS>(plus, bound), plus);
        }
        if (isOpX<BSUB>(e)) {
          Expr minus = mk<MINUS>(e->left(), e->right());
          auto wit = bitwidths.find(e);
          assert(wit != bitwidths.end());
          int width = wit->second;
          mpz_class upperBound;
          mpz_ui_pow_ui(upperBound.get_mpz_t(), 2, width);
          Expr bound = mkTerm(upperBound, e->getFactory());
          return mk<ITE>(mk<LT>(minus, mkTerm(mpz_class(0), e->getFactory())), mk<PLUS>(minus, bound), minus);
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
        if (isOpX<BAND>(e)) {
          // MB: abstract for now
          Expr var = bind::intConst(mkTerm<std::string>(getFreshName(), e->getFactory()));
          abstractionsMap[e] = var;
          return var;
        }
        if (isOpX<BEXTRACT>(e)) {
          if (bv::low(e) == 0 && bv::high(e) == 0) {
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
          // For now, abstract away with a fresh variable
//          std::cout << "Warning! Abstracting away bvconcat expression " << *e << std::endl;
          Expr var = bind::intConst(mkTerm<std::string>(getFreshName(), e->getFactory()));
          abstractionsMap[e] = var;
          return var;
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
        std::cout << "Case not covered yet: " << *e << std::endl;
        throw std::logic_error("Expression not covered in translation from BV to LIA!");
        return e;
      }
    }
  }
}

#endif //SEAHORN_EXPRTRANSLATIONS_H
