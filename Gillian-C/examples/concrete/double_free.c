#include <stdlib.h>

int main() {
    int *ptr = malloc(sizeof(int));
    if (ptr == NULL) {
        return 1;
    }
    
    *ptr = 42;
    
    free(ptr);
    free(ptr); // Double free error

    return 0;
}
