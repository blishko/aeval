#include "deep/TheorefCHCsolver.hpp"

using namespace ufo;
using namespace std;

static inline bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  bool spacer = getBoolValue("--spacer", false, argc, argv);
  solve(string(argv[argc-1]), spacer); // GF: to add more options
  return 0;
}
