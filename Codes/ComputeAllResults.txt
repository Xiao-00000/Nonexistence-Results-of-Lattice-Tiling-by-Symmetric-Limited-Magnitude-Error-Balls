# ========================================================================
# Maple loop over all 2 <= t <= 10, 1 <= k <= 10, and all primes 3 <= p <= 29,
# implementing Theorem 1.2 of
# "On Lattice Tilings by Symmetric Limited Magnitude Error Balls:
#  Q-Polynomials and Ideal Characterization".
# Output: print(t, k, p, period, excluded), where
#   period = p^(2 + floor(log[p](t))) and excluded is the set of residue
#   classes n (1 <= n <= period; n = period represents the residue class
#   0 mod period) for which no lattice tiling of Z^n by B(n,t,k,k) exists.
# This produces the raw data of Appendix B. Variable names follow
# Appendix A Listing 1 of the paper.
# ========================================================================

restart;
with(PolynomialIdeals):

# |B(n,t,k,k)| = sum_{i=0..t} (2k)^i * binomial(n,i)
ballSize := (nn, t, k) -> add((2*k)^i * binomial(nn, i), i = 0..t);

for t from 2 to 10 do
  for k from 1 to 10 do
    mul1 := 1;
    for i from 2 to 10 do
      p := ithprime(i);
      period := p^(2 + floor(log[p](t))); # period of |B(n,t,k,k)| mod p^2

      # Step 1: candidates n with p | |B| and p^2 !| |B| (hypothesis of Theorem 1.2)
      candidates := {};
      for n from 1 to period do
        if ballSize(n, t, k) mod p = 0 and ballSize(n, t, k) mod p^2 <> 0 then
          candidates := candidates union {n};
        end if;
      end do:
      unassign('n');

      # Step 2: Q^m for m = 1,...,(p-1)/2 via Theorem 1.1
      logSeries := series(ln(1 + 2*q*add(cosh(b*x), b = 1..k)), x, p):
      for ii from 1 to p-1 do
        if ii::odd then
          a[ii] := 0;
        else
          a[ii] := ii! * coeff(logSeries, x, ii) * Y[ii/2];
        end if;
      end do:
      for m from 1 to (p-1)/2 do
        Q[m] := expand(coeff(series((1 + 2*k*q)^n / (1-q)
                * CompleteBellB(2*m, seq(a[jj], jj = 1..2*m)), q, t+2), q, t)):
      end do:

      # Step 3: ideal-membership test of Theorem 1.2 over F_p
      excluded := {};
      for nn in candidates do
        J := PolynomialIdeal(seq(eval(Q[ii], n = nn), ii = 1..(p-1)/2 - 1),
                             characteristic = p):
        if eval(Q[(p-1)/2], n = nn) in J then
          excluded := excluded union {nn};
        end if;
      end do:

      print(t, k, p, period, excluded);
      mul1 := mul1 * (1 - numelems(excluded)/(period*1.0));
    end do;
    # print("@", t, k, 1 - mul1);   # excluded fraction for Table 1 of the paper
  end do;
end do:
