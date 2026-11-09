#include <stdio.h>
#include <z3.h>

int main() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    unsigned major, minor, build, rev;
    Z3_get_version(&major, &minor, &build, &rev);
    printf("Native C Z3 Version: %u.%u.%u.%u\n", major, minor, build, rev);
    
    Z3_del_context(ctx);
    return 0;
}
