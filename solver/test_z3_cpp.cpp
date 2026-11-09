#include <iostream>
#include <z3++.h>

int main() {
    try {
        z3::context ctx;
        z3::solver s(ctx);
        z3::expr x = ctx.bool_const("x");
        z3::expr y = ctx.bool_const("y");
        s.add(x || y);
        s.add(!x);
        if (s.check() == z3::sat) {
            std::cout << "Z3 C++ SAT: y = " << s.get_model().eval(y) << std::endl;
        }
    } catch (z3::exception& e) {
        std::cerr << "Z3 Error: " << e << std::endl;
    }
    return 0;
}
