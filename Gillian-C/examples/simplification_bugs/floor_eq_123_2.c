#include <gillian-c/gillian-c.h>

/*@ spec eq_bug(temp) {
  requires: (temp == float(#temp))
  ensures:  (ret == int(40));
            (ret == int(-1))
} */
int eq_bug(double temp) {
    int whole = (int) temp;
    if (whole == 20) {
        return (int)(temp / 0.5);
    }
    return -1;
}
