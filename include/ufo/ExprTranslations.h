//
// Created by Martin Blicha on 31.10.19.
//

#ifndef SEAHORN_EXPRTRANSLATIONS_H
#define SEAHORN_EXPRTRANSLATIONS_H

#include "Expr.hpp"

namespace expr {
  namespace op {
    namespace bv {

      class BV2LIATranslator {
      public:
        Expr operator()(Expr e);

      private:
        Expr _bv2lia(Expr e);

        std::map<Expr, Expr> varMap;
      };

      Expr BV2LIATranslator::operator()(Expr e) {
        return this->_bv2lia(e);
      }

      Expr BV2LIATranslator::_bv2lia(Expr e) {
        // Assummes the children have already been translated
//      if (isOpX<AND>(e) || isOpX<OR>(e) || isOpX<EQ>(e) || isOpX<NEQ>(e)) {
//        Expr left = _bv2lia(e->left());
//        Expr right = _bv2lia(e->right());
//        return mk(e->op(), left, right);
//      }
//      if (isOpX<ITE>(e)) {
//        Expr cond = _bv2lia(e->arg(0));
//        Expr t_branch = _bv2lia(e->arg(1));
//        Expr f_branch = _bv2lia(e->arg(2));
//        return mk<ITE>(cond, t_branch, f_branch);
//      }
        auto it = varMap.find(e);
        if (it != varMap.end()) { return it->second; }
        if (isOpX<AND>(e) || isOpX<OR>(e) || isOpX<EQ>(e) || isOpX<NEQ>(e) || isOpX<ITE>(e)
//            || bind::isFdecl<BOOL_TY>(e)
          )
        {
          return e;
        }
        if (op::bv::is_bvnum(e)) {
          Expr val = e->arg(0);
          return val;
        }
        if (is_bvconst(e) || is_bvvar(e)) {
          Expr name = is_bvconst(e) ? e->first()->first() : e->first();
//          std::cout << "Name of var:" << *name << std::endl;
          Expr ret = bind::intConst(name);
          varMap[e] = ret;
          return ret;
        }
        if (isOpX<BADD>(e)) {
          return mk<PLUS>(e->left(), e->right());
        }
        if (isOpX<BSUB>(e)) {
          return mk<MINUS>(e->left(), e->right());
        }
        if (isOpX<BVSORT>(e)) {
          unsigned int w = bv::width(e);
          return w == 1 ? sort::boolTy(e->getFactory()) : sort::intTy(e->getFactory());
        }
//        std::cout << "Case not covered yet: " << *e
//        //<< " op is: " << e->op()
//        << std::endl;
//        throw std::logic_error("Case not covered yet!");
        return e;
      }
    }
  }
}

#endif //SEAHORN_EXPRTRANSLATIONS_H
