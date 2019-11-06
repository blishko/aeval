#ifndef __EXPR_BV__HH_
#define __EXPR_BV__HH_

/** Bit-Vector expressions 
    
 * This file is included from middle of Expr.hpp
 */
namespace expr
{
  namespace op
  {
    namespace bv
    {
      struct BvSort
      {
        unsigned m_width;
        BvSort (unsigned width) : m_width (width) {}
        BvSort (const BvSort &o) : m_width (o.m_width) {}
        
 	bool operator< (const BvSort &b) const { return m_width < b.m_width; }
	bool operator== (const BvSort &b) const { return m_width == b.m_width; }
	bool operator!= (const BvSort &b) const { return m_width != b.m_width; }
	
	size_t hash () const
	{
	  std::hash<unsigned> hasher;
	  return hasher (m_width);
	}
	
	void Print (std::ostream &OS) const { OS << "bv(" << m_width << ")"; }	
      };
      inline std::ostream &operator<< (std::ostream &OS, const BvSort &b)
      {
	b.Print (OS);
	return OS;
      }       
    }
  }
  
  template<> struct TerminalTrait<const op::bv::BvSort>
  {
    typedef const op::bv::BvSort value_type;
    
    static inline void print (std::ostream &OS, 
			      const op::bv::BvSort &b, 
			      int depth, bool brkt) { OS << b; }
    static inline bool less (const op::bv::BvSort &b1, 
			     const op::bv::BvSort &b2)
    { return b1 < b2; }
	
    static inline bool equal_to (const op::bv::BvSort &b1, 
				 const op::bv::BvSort &b2)
    { return b1 == b2; }
	
    static inline size_t hash (const op::bv::BvSort &b) 
    { return b.hash (); }
  };
  
  namespace op
  {
    typedef Terminal<const bv::BvSort> BVSORT;
    
    namespace bv
    {
      inline Expr bvsort (unsigned width, ExprFactory &efac)
      {return mkTerm<const BvSort> (BvSort (width), efac);}
      
      inline unsigned width (Expr bvsort)
      {return getTerm<const BvSort>(bvsort).m_width;}
      
      /// Bit-vector numeral of a given sort
      /// num is an integer numeral, and bvsort is a bit-vector sort
      inline Expr bvnum (Expr num, Expr bvsort)
      {return bind::bind (num, bvsort);}
      
      /// bit-vector numeral of an arbitrary precision integer
      inline Expr bvnum (mpz_class num, unsigned bwidth, ExprFactory &efac)
      {return bvnum (mkTerm (num, efac), bvsort (bwidth, efac));}
      
      /// true if v is a bit-vector numeral
      inline bool is_bvnum (Expr v)
      {
        return isOpX<BIND> (v) && v->arity () == 2 &&
          isOpX<MPZ> (v->arg (0)) && isOpX<BVSORT> (v->arg (1));
      }

      /// true if v is a bit-vector variable
      inline bool is_bvconst (Expr v)
      {
        return isOpX<FAPP> (v) &&
          isOpX<FDECL> (v->first()) && v->first()->arity () == 2 &&
          isOpX<BVSORT> (v->first()->arg (1));
      }
      
      /// true if v is a bit-vector variable
      inline bool is_bvvar (Expr v)
      {
        return isOpX<BIND> (v) && v->arity () >= 2 &&
          !isOpX<MPZ> (v->left()) && isOpX<BVSORT> (v->right());
      }

      inline mpz_class toMpz (Expr v)
      {
        assert (is_bvnum (v));
        return getTerm<mpz_class> (v->arg (0));
      }


      inline Expr bvConst (Expr v, unsigned width)
      {
        Expr sort = bvsort (width, v->efac ());
        return bind::mkConst (v, sort);
      }

      inline std::string constToBinary(Expr c) {
        assert (is_bvnum (c));
        unsigned width = bv::width(c->right());
        auto mpz = toMpz(c);
        std::string r = mpz.get_str(2);
        // add leading zeroes if necessary get the full width
        if (r.size() < width) {
          r = std::string((width - r.size()), '0') + r;
        }
        return r;
      }

      inline Expr constFromBinary(std::string const& str, unsigned width, ExprFactory& fact) {
        assert(str.size() == width);
        if (str.size() != width) {
          // TODO: take the "width" number of bits from str
          throw std::logic_error("Not implemented yet!");
        }
        auto mpz = mpz_class(str, 2);
        Expr val = mkTerm<mpz_class>(mpz, fact);
        Expr c = bvnum(val, bvsort(width, fact));
        return c;
      }
      
      
    }
    
    NOP_BASE(BvOp)
    NOP(BNOT,"bvnot",FUNCTIONAL,BvOp)
    NOP(BREDAND,"bvredand",FUNCTIONAL,BvOp)
    NOP(BREDOR,"bvredor",FUNCTIONAL,BvOp)
    NOP(BAND,"bvand",FUNCTIONAL,BvOp)
    NOP(BOR,"bvor",FUNCTIONAL,BvOp)
    NOP(BXOR,"bvxor",FUNCTIONAL,BvOp)
    NOP(BNAND,"bvnand",FUNCTIONAL,BvOp)
    NOP(BNOR,"bvnor",FUNCTIONAL,BvOp)
    NOP(BXNOR,"bvxnor",FUNCTIONAL,BvOp)
    NOP(BNEG,"bvneg",FUNCTIONAL,BvOp)
    NOP(BADD,"bvadd",FUNCTIONAL,BvOp)
    NOP(BSUB,"bvsub",FUNCTIONAL,BvOp)
    NOP(BMUL,"bvmul",FUNCTIONAL,BvOp)
    NOP(BUDIV,"bvudiv",FUNCTIONAL,BvOp)
    NOP(BSDIV,"bvsdiv",FUNCTIONAL,BvOp)
    NOP(BUREM,"bvurem",FUNCTIONAL,BvOp)
    NOP(BSREM,"bvsrem",FUNCTIONAL,BvOp)
    NOP(BSMOD,"bvsmod",FUNCTIONAL,BvOp)
    NOP(BULT,"bvult",FUNCTIONAL,BvOp)
    NOP(BSLT,"bvslt",FUNCTIONAL,BvOp)
    NOP(BULE,"bvule",FUNCTIONAL,BvOp)
    NOP(BSLE,"bvsle",FUNCTIONAL,BvOp)
    NOP(BUGE,"bvuge",FUNCTIONAL,BvOp)
    NOP(BSGE,"bvsge",FUNCTIONAL,BvOp)
    NOP(BUGT,"bvugt",FUNCTIONAL,BvOp)
    NOP(BSGT,"bvsgt",FUNCTIONAL,BvOp)
    NOP(BCONCAT,"concat",FUNCTIONAL,BvOp)
    NOP(BEXTRACT,"extract",FUNCTIONAL,BvOp)
    NOP(BSEXT,"bvsext",FUNCTIONAL,BvOp)
    NOP(BZEXT,"bvzext",FUNCTIONAL,BvOp)
    NOP(BREPEAT,"bvrepeat",FUNCTIONAL,BvOp)
    NOP(BSHL,"bvshl",FUNCTIONAL,BvOp)
    NOP(BLSHR,"bvlshr",FUNCTIONAL,BvOp)
    NOP(BASHR,"bvashr",FUNCTIONAL,BvOp)
    NOP(BROTATE_LEFT,"bvrotleft",FUNCTIONAL,BvOp)
    NOP(BROTATE_RIGHT,"bvrotright",FUNCTIONAL,BvOp)
    NOP(BEXT_ROTATE_LEFT,"bvextrotleft",FUNCTIONAL,BvOp)
    NOP(BEXT_ROTATE_RIGHT,"bvextrotright",FUNCTIONAL,BvOp)
    NOP(INT2BV,"int2bv",FUNCTIONAL,BvOp)
    NOP(BV2INT,"bv2int",FUNCTIONAL,BvOp)
    NOP(BV2BOOL,"bv2bool",FUNCTIONAL,BvOp)
    NOP(BOOL2BV,"bool2bv",FUNCTIONAL,BvOp)

    namespace bv
    {
      /* XXX Add helper methods as needed */

      inline Expr bvnot (Expr v) {return mk<BNOT> (v);}
      inline Expr bvadd (Expr a, Expr b) { return mk<BADD> (a, b); }
      inline Expr bvule (Expr f, Expr s) { return mk<BULE> (f,s); }
      inline Expr bvuge (Expr f, Expr s) { return mk<BUGE> (f,s); }
      inline Expr bvult (Expr f, Expr s) { return mk<BULT> (f,s); }
      inline Expr bvugt (Expr f, Expr s) { return mk<BUGT> (f,s); }
      inline Expr bvsge (Expr f, Expr s) { return mk<BSGE> (f,s); }
      inline Expr bvsgt (Expr f, Expr s) { return mk<BSGT> (f,s); }
      inline Expr bvsle (Expr f, Expr s) { return mk<BSLE> (f,s); }
      inline Expr bvslt (Expr f, Expr s) { return mk<BSLT> (f,s); }
      inline Expr frombool(Expr f)       { return mk<BOOL2BV>(f); }
      inline Expr tobool(Expr f);

      inline bool isBVComparison(Expr e) {
        return isOp<BvOp>(e) && (isOpX<BULT>(e) || isOpX<BULE>(e)
                                 || isOpX<BUGT>(e) || isOpX<BUGE>(e)
                                 || isOpX<BSLT>(e) || isOpX<BSLE>(e) || isOpX<BSGT>(e) || isOpX<BSGE>(e));
      }
      
      inline Expr extract (unsigned high, unsigned low, Expr v)
      {
//        assert (high > low);
        return mk<BEXTRACT> (mkTerm<unsigned> (high, v->efac ()),
                             mkTerm<unsigned> (low, v->efac ()), v);
      }
      
      /// high bit to extract
      inline unsigned high (Expr v) {return getTerm<unsigned> (v->arg (0));}
      /// low bit to extract
      inline unsigned low (Expr v) {return getTerm<unsigned> (v->arg (1));}
      /// bv argument to extract
      inline Expr earg (Expr v) {return v->arg (2);}
      
      inline Expr sext (Expr v, unsigned width)
      {return mk<BSEXT> (v, bvsort (width, v->efac ()));}
      
      inline Expr zext (Expr v, unsigned width) 
      {return mk<BZEXT> (v, bvsort (width, v->efac ()));}

      inline Expr tobool(Expr e) {
        if (isOpX<BOOL2BV>(e)) { return e->first(); }
        if (is_bvnum(e) && width(e->arg(1)) == 1)
        {
          Expr val = e->arg(0);
          int ival = boost::lexical_cast<int>(val);
          assert(ival == 0 || ival == 1);
          return ival == 0 ? mk<FALSE>(e->getFactory()) : mk<TRUE>(e->getFactory());
        }
        if (isOpX<BNOT>(e)) {
          return mk<NEG>(tobool(e->first()));
        }
        return mk<BV2BOOL>(e);
      }
      
      inline Expr toIsZero(Expr e) {
//        std::cout << *e << std::endl;
        bool topLevelCheck = isOpX<AND>(e) || (isOpX<NEG>(e) && isOpX<OR>(e->first()));
        if (!topLevelCheck) { return nullptr; }
        bool negated = isOpX<NEG>(e);
        Expr root = negated ? e->first() : e;
        Expr actualArg = nullptr;
        std::vector<unsigned> indices;
        for (auto it = root->args_begin(); it != root->args_end(); ++it) {
          if (!negated && !isOpX<NEG>(*it)) { return nullptr; }
          Expr child = negated ? *it : (*it)->first();
          if (!isOpX<BV2BOOL>(child)) { return nullptr; }
          child = child->first();
          if (!isOpX<BEXTRACT>(child)) { return nullptr; }
          if (actualArg == nullptr) { actualArg = earg(child); }
          if (actualArg != earg(child)) {return nullptr; }
          unsigned h = high(child);
          unsigned l = low(child);
          for (; l <= h; ++l) {
            indices.push_back(l);
          }
        }
        std::sort(indices.begin(), indices.end());
        for (int i = 0; i < indices.size() - 1; ++i) {
          if (indices[i+1] != indices[i] + 1) { return nullptr; }
        }
        // Indices are consecutive, it is just a check if the actualArg is 0!
        Expr extr = extract(indices.back(), indices[0], actualArg);
        int w = indices.back() - indices[0] + 1;
        Expr res = mk<EQ>(extr, bvnum(mkTerm<mpz_class>(mpz_class(0), e->getFactory()), bvsort(w, e->getFactory())));
        return res;
      }
    }
    
    namespace bind
    {
      class IsVVar : public std::unary_function<Expr,bool>
      {
      public:
        bool operator () (Expr e)
        {
          return isIntVar(e) || isRealVar(e) || isBoolVar(e) || bv::is_bvvar(e) || isVar<ARRAY_TY> (e);
        }
      };
    }

  }
}


#endif /*  __EXPR_BV__HH_ */
