
(* :Title: The Wright omega function *)

(* :Author: J. M. *)

(* :Summary:

     This package implements the Wright omega function, a function cognate to the Lambert W function.

 *)

(* :Copyright:

     © 2015-2019 by J. M. (pleasureoffiguring(AT)gmail(DOT)com)
     This work is free. It comes without any warranty, to the extent permitted by applicable law.
     You can redistribute and/or modify it under the terms of the MIT License.

 *)

(* :Package Version: 1.0 *)

(* :Mathematica Version: 8.0 *)

(* :History:

     1.0 - initial release

*)

(* :Keywords:
     Wright omega function, Lambert W function *)

(* :References:

     Corless R. M., Jeffrey D. J. (2002) The Wright omega function.
         In: Calmet J. et al. (eds.) Artificial Intelligence, Automated Reasoning, and Symbolic Computation. AISC 2002, Calculemus 2002, p.76-89. doi:10.1007/3-540-45470-5_10
         Available from http://orcca.on.ca/TechReports/2000/TR-00-12.html

     Corless R. M., Jeffrey D. J. (2004) Computer Algebra Support for the Wright omega function.
         Available from http://www.orcca.on.ca/TechReports/2004/TR-04-03.html

     Corless R. M., Jeffrey D. J. (2004) Complex Numerical Values of the Wright omega function.
         Available from http://www.orcca.on.ca/TechReports/2004/TR-04-04.html

     Lawrence P. W., Corless R. M., Jeffrey D. J. (2012) Algorithm 917: Complex Double-Precision Evaluation of the Wright $\omega$ Function.
         ACM Trans. Math. Soft. 38 (3), Article No. 20 doi:10.1145/2168773.2168779

 *)

(* :Warnings:

     adds evaluation rules for ProductLog.

*)

 (* :Discussion:

     The package provides an implementation of the Wright omega function. Different series approximations are used in different regions
     of the complex plane, and this initial approximation is then improved with a high-order iteration (Halley, FSC).

 *)

(* :Limitations:

     Currently, the implementation uses fixed-order iteration methods for arbitrary-precision evaluation.
     It might be more efficient to use either better approximations or variable-order iterations, but this still needs to be thoroughly investigated.
     Some symbolic computation is supported, but it is not extensive.

*)

BeginPackage["Wright`"]
Unprotect[WrightOmega];

(* --- usage messages --- *)

WrightOmega::usage = "\!\(\*RowBox[{\"WrightOmega\", \"[\", StyleBox[\"z\", \"TI\"], \"]\"}]\) is the Wright omega function \!\(\*RowBox[{\"\[Omega]\", \"(\", StyleBox[\"z\", \"TI\"], \")\"}]\)."

Begin["`Private`"]

unwindK[z_] := Ceiling[(Im[z] - Pi)/(2 Pi)]

wrightExplicit[z_] := ProductLog[unwindK[z], Exp[z]]

(* Eulerian number of the second kind *)

SetAttributes[Eulerian2Number, Listable];
Eulerian2Number[n_Integer?NonNegative, k_Integer?NonNegative] := Block[{j}, 
           If[n == k == 0, 1, Sum[(-1)^(n + j) Binomial[2 n + 1, j] StirlingS1[2 n - k - j, n - k - j], {j, 0, n - k - 1}, Method -> "Procedural"]]]

(*

(* implementation from Combinatorica.m *)

Eulerian2Number[n_Integer?NonNegative, k_Integer?NonNegative] := Block[{$RecursionLimit = Infinity}, Eulerian2[n, k]]
Eulerian2[0, k_Integer] := Boole[k == 0]
Eulerian2[n_Integer, 0] := 1
Eulerian2[n_Integer, k_Integer] /; n <= k := 0
Eulerian2[n_Integer, k_Integer] := Eulerian2[n, k] =
           (k + 1) Eulerian2[n - 1, k] + (2 n - 1 - k) Eulerian2[n - 1, k - 1]

*)

(* coefficients involved in the Stirling expansion of the factorial; https://doi.org/10.2307/2324749 *)

SetAttributes[marsagliaA, Listable];
marsagliaA[0] = marsagliaA[1] = 1;
marsagliaA[k_Integer?Positive] := marsagliaA[k] = Block[{j},
              (marsagliaA[k - 1] - Sum[j marsagliaA[j] marsagliaA[k - j + 1], {j, 2, k - 1}, Method -> "Procedural"])/(k + 1)]

(* initial series approximations for the Wright function *)

(* Taylor series for Wright function *)

wrightQ[n_Integer, v_] := v FromDigits[Eulerian2Number[n - 1, Range[n - 1, 0, -1]], -v]

wrightPowerSeries[z_?NumberQ, tol_] := Module[{v = 1, h, k, res, tm, tt},
         h = (z - 1)/(1 + v);
         res = v (1 + h (1 + h (1 + (1 - 2 v) h/(3 (1 + v)))/(2 (1 + v))));
         tt = (h/24) (h/(1 + v))^3;
         tm = v (2 (3 v - 4) v + 1) tt;
         k = 4;
         While[Abs[tm] > tol Abs[res],
                  res += tm; k++; tt *= h/(1 + v)/k;
                  tm = wrightQ[k, v] tt];
         res + tm]

(* series about -Infinity *)

wrightExpSeries[z_?NumberQ, tol_] := Module[{ez = Exp[z], k, res, tm},
         res = ez (1 + ez ((3/2 - 8 ez/3) ez - 1));
         tm = 125 ez^5/24;
         k = 5;
         While[Abs[tm] > tol Abs[res],
                  res += tm; k++;
                  tm *= -ez/(1 - 1/k)^(k - 2)];
         res + tm]

(* series about Infinity *)

wrightLogSeries[z_?NumberQ, lz_?NumberQ, tol_] := Module[{iz = 1/z, k, res, tm, tt},
         res = z - lz + (1 + (lz/2 - 1) iz) lz iz;
         tt = iz^3; tm = lz ((lz/3 - 3/2) lz + 1) tt;
         k = 3;
         While[Abs[tm] > tol Abs[res],
                  res += tm; k++; tt *= -iz;
                  tm = Sum[StirlingS1[k, k - j + 1]/j! lz^j, {j, k}, Method -> "Procedural"] tt];
         res + tm]

(* series about -1 +/- Pi I *)

wrightSingularSeries[p_?NumberQ, tol_] := Module[{k, res, tm, tt},
         res = 1 + p (1 + p/3 (1 + p/6 (1/2 - p/15)));
         tt = p^5; tm = tt/4320;
         k = 5;
         While[Abs[tm] > tol Abs[res],
                  res += tm; k++; tt *= p;
                  tm = marsagliaA[k] tt];
         res + tm]

(* initial low-precision approximation *)

wrightMP[z_?NumberQ] := Module[{tol = 1.*^-4, itr, om, res, s, t, tt, x, y, zf},
         zf = SetPrecision[z, If[$MinMachineNumber < Abs[z] < $MaxMachineNumber, MachinePrecision, $MachinePrecision]];
         {x, y} = Through[{Re, Im}[zf]];
         om = NumericalMath`FixedPrecisionEvaluate[
                                Which[(-2 < x <= 1 && -1 <= y <= 1) || (-2 < x && Abs[zf - 1] <= Pi),
                                          wrightPowerSeries[zf, tol],
                                          x <= -2 && -Pi < y <= Pi,
                                          wrightExpSeries[zf, tol],
                                          -2 < x <= 1 && 1 < y < 2 Pi,
                                          t = -I Conjugate[Sqrt[Conjugate[2 (zf + 1 - I Pi)]]];
                                          -wrightSingularSeries[t, tol],
                                          -2 < x <= 1 && -2 Pi < y < -1,
                                          t = I Conjugate[Sqrt[Conjugate[2 (zf + 1 + I Pi)]]];
                                          -wrightSingularSeries[t, tol],
                                          x <= -2 && 3 (x + 1)/4 <= y + Pi <= 0,
                                          t = zf + I Pi; wrightLogSeries[t, Log[-t], tol],
                                          x <= -2 && 0 <= y - Pi <= -3 (x + 1)/4,
                                          t = zf - I Pi; wrightLogSeries[t, Log[-t], tol],
                                          True, wrightLogSeries[zf, Log[zf], tol]],
                                $MachinePrecision];
         s = 1;
         If[x <= -99/100 && (Abs[y - Pi] <= 1/100 || Abs[y + Pi] <= 1/100), (* regularization *)
             s = -1; If[Abs[y - Pi] <= 1/100, zf -= I Pi, zf += I Pi]];
         om *= s; itr = 0;
         NumericalMath`FixedPrecisionEvaluate[
                       While[t = s om; res = zf - t - Log[om];
                                t += 1; tt = t res;
                                If[tt != 0, tt /= t^2 - res/2]; (* Halley iteration *)
                                om *= 1 + tt; itr++;
                                Abs[(4 om + 1) res^3] > 12 Abs[t^4] $MachineEpsilon && itr < 4],
                       $MachinePrecision];
         N[s om]]

(* main iteration function *)

iWright[z_?InexactNumberQ] := Module[{prec = Internal`EffectivePrecision[z], ip, itr, om, pad, res, s, t, tt, tol, x, y, zf},
 {x, y} = Through[{Re, Im}[zf = z]]; pad = 5;
 ip = Max[$MachinePrecision, Quotient[Ceiling[prec], 4]];
 om = NumericalMath`RaisePrecision[wrightMP[zf], ip];
 s = 1;
 If[x <= -99/100 && (Abs[y - Pi] <= 1/100 || Abs[y + Pi] <= 1/100), (* regularization *)
     s = -1; If[Abs[y - Pi] <= 1/100, zf -= I Pi, zf += I Pi]];
 om *= s; itr = 0;  tol = 10^(-prec - pad);
 While[t = s om; res = zf - t - Log[om]; t += 1;
          tt = t (t + 2 res/3);
          tt = (res/t) (tt - res/2)/(tt - res); (* quartically-convergent iteration of Fritsch/Shafer/Crowley type *)
          om *= 1 + tt;
          ip *= 4; ip = Min[ip, Max[$MachinePrecision, prec + pad]];
          om = NumericalMath`RaisePrecision[om, ip]; itr++;
          Abs[(2 om (om - 4) - 1) res^4] > 72 Abs[t^6] tol && itr < 10];
  If[itr < 10, SetPrecision[s om, prec], $Failed]]

(* main function evaluation *)

(* special cases *)

Scan[(WrightOmega[First[#]] = Last[#]) &, {{0, ProductLog[1]}, {1, 1}, {E + 1, E}, {I Pi - 1, -1}, {-I Pi - 1, -1}}]

WrightOmega[d : DirectedInfinity[dir_?NumericQ]] := If[Re[dir] <= -1 && -Pi < Im[dir] < Pi, 0, d];
WrightOmega[ComplexInfinity] := ComplexInfinity

WrightOmega[c_. Log[z_]] /; Positive[c] && NumericQ[z] := ProductLog[z^c];
WrightOmega[c_. Log[z_] + Pi k_.] /; Positive[c] && NumericQ[z] && EvenQ[-I k] := ProductLog[Quotient[-I k, 2], z^c]

WrightOmega[z_ + Log[z_]] /; NumericQ[z] := z

(* numerical evaluation *)

WrightOmega[z_] := With[{res = iWright[z]}, res /; NumberQ[res]]

HoldPattern[Except[WrightOmega[_], WrightOmega[w___]]] := (ArgumentCountQ[WrightOmega, Length[{w}], 1, 1]; 1 /; False)
SyntaxInformation[WrightOmega] = {"ArgumentsPattern" -> {_}};
SetAttributes[WrightOmega, {Listable, NumericFunction}];

(* derivative *)

WrightOmega /: Derivative[n_Integer?NonNegative][WrightOmega] := Evaluate[wrightQ[n, WrightOmega[#]]]/(1 + WrightOmega[#])^(2 n - 1) &

(* inverse function *)

InverseFunction[WrightOmega] ^= # + Log[#] &

(* TraditionalForm formatting *)

WrightOmega /: MakeBoxes[WrightOmega[z_], TraditionalForm] := RowBox[{InterpretationBox["\[Omega]", WrightOmega, Editable -> False, Selectable -> False, Tooltip -> "WrightOmega"], "(", ToBoxes[z], ")"}]

(* additional evaluation rules for ProductLog *)

protected = Unprotect[ProductLog]

ProductLog /: ProductLog[k_, z_] /; NumericQ[k] && ! IntegerQ[k] := WrightOmega[Log[z] + 2 Pi I k]

Derivative[1, 0][ProductLog] ^= (2 I Pi ProductLog[#1, #2])/(1 + ProductLog[#1, #2]) &

ProductLog /: Derivative[k_Integer?Positive, n_Integer?Positive][ProductLog] := Derivative[k, 0][Derivative[0, n][ProductLog]]

Protect[ Evaluate[protected] ]

End[ ]

SetAttributes[WrightOmega, ReadProtected];
Protect[WrightOmega];

EndPackage[ ]