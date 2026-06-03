#include <stdlib.h>

int main() {
    int *ptr = malloc(sizeof(int));
    if (ptr == NULL) {
        return 1;
    }
    
    *ptr = 42;
    
    // Missing free(ptr) causes a memory leak
    
    return 0;
}
