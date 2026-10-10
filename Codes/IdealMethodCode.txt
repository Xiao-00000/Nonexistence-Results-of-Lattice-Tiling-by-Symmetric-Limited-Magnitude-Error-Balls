# ========================================================================
# Maple implementation of Theorem 1.2 for arbitrary t, k and odd prime p.
# Output: residue classes n (mod period) for which no lattice tiling of
# Z^n by B(n,t,k,k) exists.
# (Appendix A, Listing 1 of the paper.)
# ========================================================================

restart;

t := 4: k := 3: p := 11: # set t, k, p as needed
period := p^(2 + floor(log[p](t))); # period of |B(n,t,k,k)| mod p^2

# |B(n,t,k,k)| = sum_{i=0..t} (2k)^i * binomial(n,i)
ballSize := (nn, t, k) -> add((2*k)^i * binomial(nn, i), i = 0..t);

# Step 1: candidates n with p | |B| and p^2 !| |B| (hypothesis of Theorem 1.2)
candidates := {}:
for nn from 1 to period do
  if ballSize(nn, t, k) mod p = 0 and ballSize(nn, t, k) mod p^2 <> 0 then
    candidates := candidates union {nn};
  end if;
end do:

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
with(PolynomialIdeals):
excluded := {}:
for nn in candidates do
  J := PolynomialIdeal(seq(eval(Q[ii], n = nn), ii = 1..(p-1)/2 - 1),
                       characteristic = p):
  if eval(Q[(p-1)/2], n = nn) in J then
    excluded := excluded union {nn};
  end if;
end do:

excluded; # nn = period represents the residue class n = 0 (mod period)
