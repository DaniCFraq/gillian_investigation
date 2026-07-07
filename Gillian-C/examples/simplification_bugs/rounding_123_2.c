#include <gillian-c/gillian-c.h>

/*@ spec display_temp(temp) {
  requires: (temp == float(#temp))
  ensures:  (ret == int(20));
            (ret == int(-1))
} */
int display_temp(double temp) {     // temp is 20.3
    int whole = (int) temp;         // whole is 20
    if (whole == 20) {              // Enters if
        return (int)(temp + 0.5);   // 20.3 + 0.5 = 20.8, (int) 21.8 = 21 but temp
                                    // is 20 because of the simplification
    }                               // With simpl on -> 20. with simpl off -> 21
                                    // Postconditions should fail
    return -1;                        
}
