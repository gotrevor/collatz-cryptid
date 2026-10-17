// E[Z_N^2]/E[Z_N]^2 under Haar, Z_N(x;t)=sum over legal length-N words of t^cost (Fornet PT1.1):
// Z_{N+1}(2m)=Z_N(3m)+t^2 Z_N(3m+1), Z_{N+1}(2m+1)=t Z_N(3m+2), args mod 2^N.  Normalized per step.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int main(int argc, char **argv) {
  int Nmax = atoi(argv[1]); double th = atof(argv[2]), t = exp(-th), mu = (1 + t + t * t) / 2;
  float *Z = malloc(sizeof(float)); Z[0] = 1;
  for (int N = 0; N < Nmax; N++) {
    uint64_t M = 1ULL << N, mask = M - 1;
    float *W = malloc(2 * M * sizeof(float));
    double s1 = 0, s2 = 0;
    for (uint64_t m = 0; m < M; m++) {
      uint64_t a = 3 * m;
      float e = (Z[a & mask] + t * t * Z[(a + 1) & mask]) / mu, o = t * Z[(a + 2) & mask] / mu;
      W[2 * m] = e; W[2 * m + 1] = o; s1 += e + o; s2 += (double)e * e + (double)o * o;
    }
    free(Z); Z = W;
    double E1 = s1 / (2.0 * M), E2 = s2 / (2.0 * M);
    if (N + 1 >= Nmax - 6) printf("theta=%.3f N=%d E[Z]=%.6f E[Z^2]/E[Z]^2=%.4f\n", th, N + 1, E1, E2 / (E1 * E1));
  }
  return 0;
}
