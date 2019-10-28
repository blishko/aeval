#include "deep/CandChecker.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

// unsigned bw_bound = 128, unsigned bval_bound = 2, bool enable_eqs = 1, bool enable_adds = 1, bool enable_bvnot = 0, bool enable_extract = 1, bool enable_concr = 1, bool enable_concr_impl = 0, bool enable_or = 1

int main (int argc, char ** argv)
{
  simpleCheck(argv[argc-1], getIntValue("--bw", 128, argc, argv),
              getIntValue("--val", 1, argc, argv), getBoolValue("--eqs", 0, argc, argv),
              getBoolValue("--adds", 0, argc, argv), getBoolValue("--bvnot", 0, argc, argv),
              getBoolValue("--ext", 0, argc, argv), getBoolValue("--conc", 0, argc, argv),
              getBoolValue("--impl", 0, argc, argv), getBoolValue("--or", 0, argc, argv));
  return 0;
}
