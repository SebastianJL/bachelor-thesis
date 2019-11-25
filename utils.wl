(* ::Package:: *)

BeginPackage["utils`"]

pdConvert::usage=
	"Convert the display form of partial derivatives from \!\(\*SuperscriptBox[\(f\), \((1, 2)\)]\)[x,y] to \!\(\*FractionBox[\(\*SuperscriptBox[\(\[PartialD]\), \(3\)]f \((x, y)\)\), \(\[PartialD]x \*SuperscriptBox[\(\[PartialD]\), \(2\)]y\)]\)"
extractSummands::usage=
	"Returns original sum with first n summands extractet."
mergeSums::usage=
	"Merge sums."
expandSum::usage=
	"Collect powers of var and expand into seperate sums."
shiftSum::usage=
	"Shift the index of the sum by shift."
	
shootingMethod::usage=
"Numerical method to solve second order ODE eigenvalue problem.
shootingMethod[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]Less0}, boundary]: Find first eigenvalue greater than \[CapitalEpsilon]Less0.
shootingMethod[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]Less0, \[CapitalEpsilon]More0}, boundary]: Find first eigenvalue between \[CapitalEpsilon]Less0 and \[CapitalEpsilon]More0.
Returns: {\[CapitalEpsilon] -> eigenvalue, InterpolatingFunction}"

shootingMethod::range=
	"The solutions at \[CapitalEpsilon]Less0 and \[CapitalEpsilon]More0 seem to both diverge in the same direction. You probably need to redefine them such that \[CapitalEpsilon]Less0 < \!\(\*SubscriptBox[\(\[CapitalEpsilon]\), \(Eigenvalue\)]\) < \[CapitalEpsilon]More0";
shootingMethod::signs=
	"sign\[CapitalEpsilon]Less = `1`, sign\[CapitalEpsilon]More = `2`"
shootingMethod::convergence=
	"Algorithm didn't converge. Returned result is probably wrong."
shootingMethod::maxIterations=
	"Finding \[CapitalEpsilon]More took more than MaxIterations. Try adjusting through the option MaxIterations."


Begin["`Private`"]

pdConvert[f_] :=
	TraditionalForm[
		f /. Derivative[inds__][g_][vars__] :> Apply[
			Defer[D[g[vars], ##]]&, Transpose[{{vars}, {inds}}] /. {{var_, 0} :> Sequence[], {var_, 1} :> {var}}]]

extractSummands[sum_Sum, index_, 0] :=
	sum
extractSummands[sum_Sum, index_, n_Integer] :=
	Block[{var, min, max, expr, summands},
		expr = sum[[1]];
		{var, min, max} = sum[[2]];
		summands = expr /. Table[{index -> i}, {i, min, min+n-1}];
		Plus@@summands + Sum[expr, {index, min+n, max}]
	] /; n > 0

shiftSum[sum_Sum, 0] := sum
shiftSum[sum_Sum, shift_Integer] :=
	sum /. Sum[expr_, lims_] :> With[
		{newSum = expr /. lims[[1]] -> lims[[1]] - shift, newLim1 = lims[[1]], newLim2 = lims[[2]] + shift, newLim3 = lims[[3]]},
		Sum[newSum, {newLim1, newLim2, newLim3}]
	]

mergeSums[expr_, shift_Integer: 0] :=
	Module[{newExpr},
		newExpr = expr //. (ca_. Sum[a_, an_]+cb_. Sum[b_, bn_]) :> With[
			{sum = Simplify[ca*a + (cb*b /. bn[[1]] -> an[[1]] + bn[[2]] - an[[2]])]},
			Sum[sum, an] /; an[[3]] == bn[[3]] == \[Infinity]
		];
		newExpr /. sum_Sum :> shiftSum[sum, shift]
	]
	
expandSum[sum_Sum, var_] :=
	sum /. Sum[a_, an_] :> Sum[Collect[a, var], an] //. Sum[a_ + b_, n_] :> Sum[a, n] + Sum[b, n]

(*Exponential falloff*)
signOfLastRoot[roots_, func_, None]:=
	(*If no root has been found, we are talking about \[CapitalEpsilon]Less, presuming func[0]\[GreaterEqual]0 & func'[0]\[GreaterEqual] 0.*)
	If[roots == {}, 1, Sign[(func)'[roots[[1, -1]]]]]
(*Finite Boundary*)
signOfLastRoot[roots_, func_, boundary_?NumericQ]:=
	Sign[func[boundary]]
	
numberOfRoots[roots_, None]:=
	Length[Flatten[roots]]
numberOfRoots[roots_, boundary_?NumericQ]:=
	Length[TakeWhile[Flatten[roots], # <= boundary &]]
		
shoot[{ode_, initCond1_, initCond2_}, y_, {x_, xmin_?NumericQ, xmax_?NumericQ}, {\[CapitalEpsilon]_, \[CapitalEpsilon]Value_?NumericQ}]:=
	Block[{interpolation, roots, solr},
		{interpolation, roots} = Reap@NDSolve[{ode /. \[CapitalEpsilon]->\[CapitalEpsilon]Value, initCond1, initCond2, WhenEvent[y[x] == 0, Sow[x]]}, y, {x, xmin, xmax}];
		interpolation = interpolation[[1, 1]];
		{interpolation, roots}]

Options[shootingMethod] = {"Verbose" -> False, "Precision" -> 5, MaxIterations -> 100, "Output" -> "Rule"}
shootingMethod[{ode_, initCond1_, initCond2_}, y_, {x_, xmin_?NumericQ, xmax_?NumericQ}, {\[CapitalEpsilon]_, \[CapitalEpsilon]Less0_?NumericQ, \[CapitalEpsilon]More0_?NumericQ},
		boundary_, OptionsPattern[]]:=
	Block[{\[CapitalEpsilon]Less=\[CapitalEpsilon]Less0, \[CapitalEpsilon]More=\[CapitalEpsilon]More0, \[CapitalEpsilon]New, roots, sign\[CapitalEpsilon]Less, sign\[CapitalEpsilon]More, signNew, interpolation, iterate},
		(*Find sign of \[CapitalEpsilon]Less.*)
		{interpolation, roots} = shoot[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]Less}];
		sign\[CapitalEpsilon]Less = signOfLastRoot[roots, y /. interpolation, boundary];
		
		(*Find sign of \[CapitalEpsilon]More.*)
		{interpolation, roots} = shoot[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]More}];
		sign\[CapitalEpsilon]More = signOfLastRoot[roots, y /. interpolation, boundary];
		
		(*Decide whether to continue or skip iteration due to malformed input.*)
		iterate = If[sign\[CapitalEpsilon]Less*sign\[CapitalEpsilon]More == -1,
			True,
			
			If[OptionValue["Verbose"], 
				Message[shootingMethod::signs, sign\[CapitalEpsilon]Less, sign\[CapitalEpsilon]More]];
			Message[shootingMethod::range];
			Message[shootingMethod::convergence];
			False,
			
			Message[shootingMethod::convergence];
			False];
		
		(*Midpoint search for Eigenvalue.*)
		\[Epsilon] = 10^(-(OptionValue["Precision"] + 1));
		While[iterate && Not[Abs[\[CapitalEpsilon]More - \[CapitalEpsilon]Less] < \[Epsilon]],
			\[CapitalEpsilon]New = (\[CapitalEpsilon]Less + \[CapitalEpsilon]More)/2;
			{interpolation, roots} = shoot[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]New}];
			signNew = signOfLastRoot[roots, y /. interpolation, boundary];
			If[OptionValue["Verbose"], Echo[{sign\[CapitalEpsilon]Less, sign\[CapitalEpsilon]More, signNew, \[CapitalEpsilon]Less, \[CapitalEpsilon]More, \[CapitalEpsilon]New, interpolation}]];
			Switch[signNew,
				sign\[CapitalEpsilon]Less, \[CapitalEpsilon]Less = \[CapitalEpsilon]New,
				sign\[CapitalEpsilon]More, \[CapitalEpsilon]More = \[CapitalEpsilon]New];];
		
		(*Return*)
		Switch[OptionValue["Output"],
			"Rule", {\[CapitalEpsilon] -> If[ValueQ[\[CapitalEpsilon]New], \[CapitalEpsilon]New, \[CapitalEpsilon]More], interpolation},
			"Value", {If[ValueQ[\[CapitalEpsilon]New], \[CapitalEpsilon]New, \[CapitalEpsilon]More], interpolation}]]

shootingMethod[{ode_, initCond1_, initCond2_}, y_, {x_, xmin_?NumericQ, xmax_?NumericQ}, {\[CapitalEpsilon]_, \[CapitalEpsilon]Less0_?NumericQ},
		boundary_, OptionsPattern[]]:=
		Block[{counter, \[CapitalEpsilon]More = 2*\[CapitalEpsilon]Less0 + 1, \[CapitalEpsilon]UpperLimit, found\[CapitalEpsilon]UpperLimit, interpolation, roots, nRoots\[CapitalEpsilon]More, nRoots\[CapitalEpsilon]Less},
			{interpolation, roots} = shoot[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]Less0}];	
			nRoots\[CapitalEpsilon]Less = numberOfRoots[roots, boundary];
			
			{interpolation, roots} = shoot[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]More}];
			nRoots\[CapitalEpsilon]More = numberOfRoots[roots, boundary];
			
			counter = 0;
			found\[CapitalEpsilon]UpperLimit = False;
			While[Not[nRoots\[CapitalEpsilon]Less + 1 == nRoots\[CapitalEpsilon]More],
				If[counter >= OptionValue[MaxIterations],
					Message[shootingMethod::maxIterations];
					Return[Null]]
							
				If[nRoots\[CapitalEpsilon]Less + 1 < nRoots\[CapitalEpsilon]More,
					found\[CapitalEpsilon]UpperLimit = True;
					\[CapitalEpsilon]UpperLimit = \[CapitalEpsilon]More;
					\[CapitalEpsilon]More = (\[CapitalEpsilon]Less0 + \[CapitalEpsilon]UpperLimit)/2,
					
					If[found\[CapitalEpsilon]UpperLimit,
						\[CapitalEpsilon]More = (\[CapitalEpsilon]More + \[CapitalEpsilon]UpperLimit)/2,
						\[CapitalEpsilon]More = \[CapitalEpsilon]UpperLimit = 2*(\[CapitalEpsilon]More - \[CapitalEpsilon]Less0)]];
				{interpolation, roots} = shoot[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]More}];
				nRoots\[CapitalEpsilon]More = numberOfRoots[roots, boundary];
				
				If[OptionValue["Verbose"],
					Echo[{nRoots\[CapitalEpsilon]Less, nRoots\[CapitalEpsilon]More, \[CapitalEpsilon]Less0, \[CapitalEpsilon]More, \[CapitalEpsilon]UpperLimit}]];
				
				counter = counter + 1];
				
			shootingMethod[{ode, initCond1, initCond2}, y, {x, xmin, xmax}, {\[CapitalEpsilon], \[CapitalEpsilon]Less0, \[CapitalEpsilon]More}, 
				boundary, "Verbose" -> OptionValue["Verbose"], "Precision" -> OptionValue["Precision"], "Output" -> OptionValue["Output"]]]
			

End[]

EndPackage[]
