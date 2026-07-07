#include <gillian-c/gillian-c.h>

/*@ spec add_bug(x) {
  requires: (x == float(#x))
  ensures:  (ret == int(0))
} */
int add_bug(double x) {
    return (int)(x + 0.5) - (int)x;
}
