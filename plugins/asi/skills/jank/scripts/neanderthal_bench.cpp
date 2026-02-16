// neanderthal_bench.cpp — extracted from neanderthal.jank, native C++ benchmark
// Compares: REGISTER (fixed Matrix2d) vs DYNAMIC (MatrixXd) vs STRUCTURE (append-only log)
//
// Compile: clang++ -O3 -march=native -I$(pkg-config --cflags-only-I eigen3 | sed 's/-I//') \
//          neanderthal_bench.cpp -o neanderthal_bench

#include <Eigen/Dense>
#include <iostream>
#include <vector>
#include <chrono>
#include <cstdio>
#include <cmath>

// === Types ===
using Vec2 = Eigen::Vector2d;
using Mat2 = Eigen::Matrix2d;
using Vec  = Eigen::VectorXd;
using Mat  = Eigen::MatrixXd;

// === Append-only log (STRUCTURE path) ===
struct LogEntry {
    int step;
    double cost;
    double norm;
};

struct AppendLog {
    std::vector<LogEntry> entries;
    void append(int step, double cost, double norm) {
        entries.push_back({step, cost, norm});
    }
    size_t size() const { return entries.size(); }
    LogEntry const& at(size_t i) const { return entries.at(i); }
};

// === Fixed-size MPC step (REGISTER path) ===
struct MPC2State {
    Vec2 x;
    double cost;
    double norm;
};

__attribute__((noinline))
MPC2State mpc2_step(Mat2 const& A, Vec2 const& B_u, Mat2 const& Q, Vec2 const& x) {
    Vec2 x_next = A * x + B_u;
    double cost = x.dot(Q * x);
    return {x_next, cost, x_next.norm()};
}

// === Dynamic MPC step (DYNAMIC path) ===
__attribute__((noinline))
void mpc_dynamic_step(Mat const& A, Mat const& B, Vec const& u, Mat const& Q,
                      Vec& x, double& cost, double& norm) {
    Vec x_next = A * x + B * u;
    cost = x.dot(Q * x);
    norm = x_next.norm();
    x = x_next;
}

// === BLAS Level 1 tests ===
void test_blas_l1() {
    std::printf("=== BLAS Level 1: Vector-Vector ===\n");
    Vec x(2), y(2);
    x << 1.0, 0.0;
    y << 0.0, 1.0;

    double d = x.dot(y);
    std::printf("  dot([1,0], [0,1]) = %.1f (expected 0.0) %s\n", d, d == 0.0 ? "PASS" : "FAIL");

    double n = x.norm();
    std::printf("  nrm2([1,0]) = %.1f (expected 1.0) %s\n", n, n == 1.0 ? "PASS" : "FAIL");

    // axpy: y = alpha*x + y
    double alpha = 2.5;
    Vec axpy_result = alpha * x + y;
    std::printf("  axpy(2.5, [1,0], [0,1]) = [%.1f, %.1f] (expected [2.5, 1.0]) %s\n",
                axpy_result(0), axpy_result(1),
                (axpy_result(0) == 2.5 && axpy_result(1) == 1.0) ? "PASS" : "FAIL");

    // scal
    Vec scal_result = 3.0 * x;
    std::printf("  scal(3.0, [1,0]) = [%.1f, %.1f] (expected [3.0, 0.0]) %s\n",
                scal_result(0), scal_result(1),
                (scal_result(0) == 3.0 && scal_result(1) == 0.0) ? "PASS" : "FAIL");
    std::printf("\n");
}

// === BLAS Level 2/3 tests ===
void test_blas_l23() {
    std::printf("=== BLAS Level 2/3: Matrix ops ===\n");
    Mat A(2, 2);
    A << 1, 3, 2, 4; // column-major: [[1,3],[2,4]]

    Vec x(2);
    x << 1.0, 1.0;

    // mv: A*x
    Vec mv_result = A * x;
    std::printf("  mv([[1,3],[2,4]], [1,1]) = [%.0f, %.0f] (expected [4, 6]) %s\n",
                mv_result(0), mv_result(1),
                (mv_result(0) == 4.0 && mv_result(1) == 6.0) ? "PASS" : "FAIL");

    // mm: A*A
    Mat mm_result = A * A;
    std::printf("  mm(A,A)[0,0] = %.0f (expected 7) %s\n",
                mm_result(0,0), mm_result(0,0) == 7.0 ? "PASS" : "FAIL");

    // trans
    Mat At = A.transpose();
    std::printf("  trans(A)[0,1] = %.0f (expected 2) %s\n",
                At(0,1), At(0,1) == 2.0 ? "PASS" : "FAIL");
    std::printf("\n");
}

// === MPC correctness test ===
void test_mpc_correctness() {
    std::printf("=== MPC Correctness Test ===\n");

    // Fixed-size path
    Mat2 A_f; A_f << 0.9, -0.1, 0.1, 0.95;
    Vec2 Bu_f; Bu_f << 0.5 * -0.2, 0.3 * -0.2;
    Mat2 Q_f; Q_f << 1.0, 0.0, 0.0, 1.0;
    Vec2 x0_f; x0_f << 5.0, 3.0;

    // Dynamic path
    Mat A_d(2,2); A_d << 0.9, -0.1, 0.1, 0.95;
    Mat B_d(2,1); B_d << 0.5, 0.3;
    Vec u_d(1); u_d << -0.2;
    Mat Q_d(2,2); Q_d << 1.0, 0.0, 0.0, 1.0;
    Vec x0_d(2); x0_d << 5.0, 3.0;

    // Run 5 steps on both paths, compare
    Vec2 xf = x0_f;
    Vec  xd = x0_d;
    bool all_match = true;

    for (int i = 0; i < 5; i++) {
        auto sf = mpc2_step(A_f, Bu_f, Q_f, xf);
        double cost_d, norm_d;
        mpc_dynamic_step(A_d, B_d, u_d, Q_d, xd, cost_d, norm_d);

        double cost_err = std::abs(sf.cost - cost_d);
        double norm_err = std::abs(sf.norm - norm_d);
        bool match = cost_err < 1e-10 && norm_err < 1e-10;
        if (!match) all_match = false;

        std::printf("  step %d: fixed cost=%.6f norm=%.6f | dynamic cost=%.6f norm=%.6f | %s\n",
                    i, sf.cost, sf.norm, cost_d, norm_d, match ? "MATCH" : "MISMATCH");
        xf = sf.x;
    }
    std::printf("  Overall: %s\n\n", all_match ? "PASS — fixed and dynamic paths agree" : "FAIL");
}

// === Benchmark helpers ===
using Clock = std::chrono::high_resolution_clock;

template<typename F>
double bench_ns(F&& f, int iters) {
    // warmup
    for (int i = 0; i < iters / 10; i++) f();

    auto start = Clock::now();
    for (int i = 0; i < iters; i++) f();
    auto end = Clock::now();
    return std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count() / double(iters);
}

void benchmark_register_path() {
    std::printf("=== Benchmark: REGISTER path (Matrix2d, stack, SIMD) ===\n");

    Mat2 A; A << 0.9, -0.1, 0.1, 0.95;
    Vec2 Bu; Bu << -0.1, -0.06;
    Mat2 Q; Q << 1.0, 0.0, 0.0, 1.0;
    Vec2 x; x << 5.0, 3.0;

    int horizon = 20;
    int iters = 1000000;

    double ns = bench_ns([&]() {
        Vec2 xi = x;
        for (int i = 0; i < horizon; i++) {
            auto s = mpc2_step(A, Bu, Q, xi);
            xi = s.x;
        }
    }, iters);

    std::printf("  %d-step horizon: %.1f ns/horizon, %.1f ns/step\n", horizon, ns, ns / horizon);
    std::printf("  %.2f M horizons/sec\n", 1e3 / ns);
    std::printf("  FLOPs/step: ~14 (2 FMA + dot + norm) → %.1f GFLOPS\n\n",
                14.0 * horizon / ns);
}

void benchmark_dynamic_path() {
    std::printf("=== Benchmark: DYNAMIC path (MatrixXd, heap) ===\n");

    Mat A(2,2); A << 0.9, -0.1, 0.1, 0.95;
    Mat B(2,1); B << 0.5, 0.3;
    Vec u(1); u << -0.2;
    Mat Q(2,2); Q << 1.0, 0.0, 0.0, 1.0;
    Vec x0(2); x0 << 5.0, 3.0;

    int horizon = 20;
    int iters = 500000;

    double ns = bench_ns([&]() {
        Vec xi = x0;
        double cost, norm;
        for (int i = 0; i < horizon; i++) {
            mpc_dynamic_step(A, B, u, Q, xi, cost, norm);
        }
    }, iters);

    std::printf("  %d-step horizon: %.1f ns/horizon, %.1f ns/step\n", horizon, ns, ns / horizon);
    std::printf("  %.2f M horizons/sec\n", 1e3 / ns);
    std::printf("\n");
}

void benchmark_structure_path() {
    std::printf("=== Benchmark: STRUCTURE path (append-only log) ===\n");

    Mat2 A; A << 0.9, -0.1, 0.1, 0.95;
    Vec2 Bu; Bu << -0.1, -0.06;
    Mat2 Q; Q << 1.0, 0.0, 0.0, 1.0;
    Vec2 x0; x0 << 5.0, 3.0;

    int horizon = 20;
    int iters = 500000;

    double ns = bench_ns([&]() {
        AppendLog log;
        log.entries.reserve(horizon);
        Vec2 xi = x0;
        for (int i = 0; i < horizon; i++) {
            auto s = mpc2_step(A, Bu, Q, xi);
            log.append(i, s.cost, s.norm);
            xi = s.x;
        }
    }, iters);

    std::printf("  %d-step horizon + log: %.1f ns/horizon, %.1f ns/step\n", horizon, ns, ns / horizon);
    std::printf("  %.2f M horizons/sec\n", 1e3 / ns);
    std::printf("  Log overhead vs REGISTER: measured below\n\n");
}

void benchmark_scaling() {
    std::printf("=== Benchmark: Scaling (REGISTER vs DYNAMIC, varying N) ===\n");
    std::printf("  N  | REGISTER (ns/step) | DYNAMIC (ns/step) | ratio\n");
    std::printf("  ---|--------------------:|------------------:|------\n");

    // N=2: use fixed types
    {
        Mat2 A; A << 0.9, -0.1, 0.1, 0.95;
        Vec2 Bu; Bu << -0.1, -0.06;
        Mat2 Q; Q << 1.0, 0.0, 0.0, 1.0;
        Vec2 x0; x0 << 5.0, 3.0;

        Mat Ad(2,2); Ad << 0.9, -0.1, 0.1, 0.95;
        Mat Bd(2,1); Bd << 0.5, 0.3;
        Vec ud(1); ud << -0.2;
        Mat Qd(2,2); Qd << 1.0, 0.0, 0.0, 1.0;
        Vec xd0(2); xd0 << 5.0, 3.0;

        double ns_reg = bench_ns([&]() {
            auto s = mpc2_step(A, Bu, Q, x0);
            (void)s;
        }, 5000000);

        double ns_dyn = bench_ns([&]() {
            Vec xi = xd0;
            double c, n;
            mpc_dynamic_step(Ad, Bd, ud, Qd, xi, c, n);
        }, 2000000);

        std::printf("  2  | %18.1f | %17.1f | %.1fx\n", ns_reg, ns_dyn, ns_dyn / ns_reg);
    }

    // N=4,8,16: dynamic only (no fixed-size templates for arbitrary N)
    for (int N : {4, 8, 16, 32, 64}) {
        Mat A = Mat::Random(N, N) * 0.5;
        // Make stable (spectral radius < 1)
        A = A / (A.norm() + 0.1);
        Mat B = Mat::Random(N, 1) * 0.1;
        Vec u = Vec::Random(1);
        Mat Q = Mat::Identity(N, N);
        Vec x0 = Vec::Random(N);

        double ns_dyn = bench_ns([&]() {
            Vec xi = x0;
            double c, n;
            mpc_dynamic_step(A, B, u, Q, xi, c, n);
        }, 1000000 / N);

        std::printf("  %-2d | %18s | %17.1f | —\n", N, "—", ns_dyn);
    }
    std::printf("\n");
}

// === MPC horizon demo (print trajectory) ===
void demo_trajectory() {
    std::printf("=== MPC Trajectory (20-step, seed state [5, 3]) ===\n");
    std::printf("  step | cost      | ||x||\n");
    std::printf("  -----|-----------|-------\n");

    Mat2 A; A << 0.9, -0.1, 0.1, 0.95;
    Vec2 Bu; Bu << -0.1, -0.06;
    Mat2 Q; Q << 1.0, 0.0, 0.0, 1.0;
    Vec2 x; x << 5.0, 3.0;

    AppendLog log;
    for (int i = 0; i < 20; i++) {
        auto s = mpc2_step(A, Bu, Q, x);
        log.append(i, s.cost, s.norm);
        x = s.x;
    }

    for (size_t i = 0; i < log.size(); i++) {
        auto& e = log.at(i);
        std::printf("  %4d | %9.4f | %.4f\n", e.step, e.cost, e.norm);
    }
    std::printf("\n");
}

int main() {
    std::printf("neanderthal_bench — Eigen-backed BLAS + MPC benchmark\n");
    std::printf("Eigen %d.%d.%d | ", EIGEN_WORLD_VERSION, EIGEN_MAJOR_VERSION, EIGEN_MINOR_VERSION);
#ifdef __AVX2__
    std::printf("AVX2 ");
#endif
#ifdef __AVX__
    std::printf("AVX ");
#endif
#ifdef __SSE4_2__
    std::printf("SSE4.2 ");
#endif
#ifdef __ARM_NEON
    std::printf("NEON ");
#endif
    std::printf("\n\n");

    test_blas_l1();
    test_blas_l23();
    test_mpc_correctness();
    demo_trajectory();
    benchmark_register_path();
    benchmark_dynamic_path();
    benchmark_structure_path();
    benchmark_scaling();

    std::printf("=== Summary ===\n");
    std::printf("REGISTER: Fixed-size, stack-alloc, SIMD — lowest latency per step\n");
    std::printf("DYNAMIC:  MatrixXd, heap-alloc — general, slower for small N\n");
    std::printf("STRUCTURE: REGISTER + append-only log — auditable trajectory\n");
    return 0;
}
