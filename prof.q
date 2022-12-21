/
	Q code profiler
	Copyright (c) 2014-2019 Leslie Goldsmith

	Licensed under the Apache License, Version 2.0 (the "License");
	you may not use this file except in compliance with the License.
	You may obtain a copy of the License at:

	http://www.apache.org/licenses/LICENSE-2.0

	Unless required by applicable law or agreed to in writing,
	software distributed under the License is distributed on an
	"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
	either express or implied.  See the License for the specific 
	language governing permissions and limitations under the 
	License.

	----------------
	
	Contains routines to profile statement execution counts and CPU
	consumption.  Functions to be profiled can be specified
	explicitly or by referencing a parent namespace (in which case
	all functions in all namespaces below it are examined).
	
	Profiling temporarily modifies a function by adding
	instrumentation logic to it.  A copy of the original function
	is first saved, and is restored when profiling is removed.
	Note that if a profiled function is modified, changes to it
	are lost when profiling is removed.

	Attribution of subcall time may not be correct in a profiled
	function that signals an event to a higher level.

	Usage information appears at the bottom of this file.

	Author:		Leslie Goldsmith
\


\d .prof

NSX:`q`Q`h`j`m`o`s`prof / Namespace exclusion list
LL:30 / Number of source chars to show

PFD:(0#`)!PFS:()
if[not type key`SV;SV:PFD]


//
// @desc Enables profiling for specified functions.
//
// @param x {symbol[]}	Specifies the names of the functions to profile.  Namespaces
//				  		are replaced by the names of the functions within them,
//				  		recursively.  If the argument is unspecified or is the empty
//				  		symbol, all functions in all non-system namespaces are profiled.
//
prof:{
	{f:$[type key x;value x;0];
		$[100h<>type f;-2 "Not a function: ",string x;
			"l"=first s:last v:value f;-2 "Locked function: ",string x;
			count t:xf[x;s];[PFD[x]:(enl last[t]j?1+til i),(i:last j:t 1)#'"inn"$0;SV[x]:f;def[x;first v 3;first t]];
			-2 "Already profiled: ",string x];
		} each fns x;
	}


//
// @desc Disables profiling for specified functions, and discards collected usage
// information.
//
// @param x {symbol[]}	Specifies the names of the functions to unprofile.  Namespaces
//				  		are replaced by the names of the functions within them,
//				  		recursively.  If the argument is unspecified or is the empty
//				  		symbol, profiling is disabled for all functions for which it
//				  		is enabled.
//
unprof:{
	{$[100h<>type f:SV x;-2 "Not profiled: ",string x;
		[x set f;{.[`.prof;(,)x;_;y]}\:[`SV`PFD;x]]];
		} each $[mt x;key SV;fns x];
	}


//
// @desc Resets profile statistics, discarding previous results.  The state of
// profiled functions is unaltered.
//
reset:{PFD[;1 2 3]*:0;PFS::()}


//
// @desc Returns the raw data representing the profile execution results.  For each
// profiled line on which execution occurred, the data includes the following:
//
//		- function name
//		- closed line number
//		- leading statement characters
//		- line execution count
//		- total time consumed on the line (including subcalls)
//		- time consumed on the line itself
//		- percentage of time consumed on the line relative to all lines
//
// Lines not executed are not included in the report.
//
// @param x {symbol[]}	Specifies the names of the functions for which execution
//				  		information is to be computed.  If the argument is unspecified
//				  		or is the empty symbol, data is returned for all profiled
//				  		functions.
//
// @return {table}		A table containing the execution report, ordered alphabetically
//						by function and then by line number.
//
data:{
	x:$[mt x;key PFD;not(&/)b:(x,:())in key PFD;[-2 "Not profiled:",/" ",'string x where not b;x where b];x];
	a:x where n:count each w:flip each PFD x; / Function names
	t:(-\)each(w:raze w)[;2 3]; / Total and own ( = total - subcall)
	asc update Pct:100*Own%(+/)Own from select from ([]Name:a;Line:(,/)til each n;Stmt:`$ssr[;"\n";" "]each w[;0];Count:w[;1];Total:t[;0];Own:t[;1]) where Count>0
	}


//
// @desc Computes a usage report summarizing the profile execution results.  For each
// profiled line on which execution occurred, the data includes the following:
//
//		- function name
//		- closed line number
//		- leading statement characters
//		- line execution count
//		- total time consumed on the line (including subcalls), in MM:SS.sss
//		- time consumed on the line itself, in MM:SS.sss
//		- percentage of time consumed on the line relative to all other lines
//
// Lines not executed are not included in the report.
//
// @param x {symbol[]}	Specifies the names of the functions for which execution
//				  		information is to be computed.  If the argument is unspecified
//				  		or is the empty symbol, the report is computed for all
//				  		profiled functions.
//
// @return {table}		A table containing the execution report, ordered by decreasing
//						own line execution time.
//
report:{
	t:`$3_''string"t"$(w:data x)`Total`Own;
	`Own xdesc update Total:first t,Own:last t,Pct:`$(.prof.ffmt[2;Pct],'"%") from w
	}


//
// Internal definitions.
//


enl:enlist
ns:~[1#.q]1#
mt:{(x~`)|x~(::)}
fns:{asc$[mt x;ff(key`.),getn ` sv'`,'(key`)except NSX;getn x]}
ff:{x where 100h=type each value each x}
getn:{(,/)getns each x}
getns:{$[type key x;$[ns value x;ff(j where not i),getn(j:` sv'x,'k)where i:ns each x k:1_key x;`.~x;ff key x;x];x]}
expand:{[msk;a] @[msk;where msk;:;a]}
trueAt:{@[x#0b;y;:;1b]}
ffmt:{("0";"")[x<count each s],'(i _'s),'".",'(i:neg x)#'s:string(_)y*/x#10}

CH:"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-`.:"


//
// @desc Defines a function within its associated namespace.
//
// @param nm {symbol}	Specifies the fully-qualified name of the function to define.
// @param c {symbol}	Specifies the context in which to define the function.
// @param f {string}	Specifies the definition of the function.
//
def:{[nm;c;f]
	d:system "d";system "d .",string c; / Set namespace
	nm set value f; / Define object (reification performed by <value> must be under proper ns)
	system "d ",string d; / Restore previous namespace
	}


//
// @desc Initializes statistics collection on function entry.
//
// @param nm {symbol}	Specifies the name of the function.
//
// @return {int}		Origin-0 index of the stack level of the new function call.
//
init:{[nm]
	-1+count PFS,:enl nm,1 1 0*.z.n / Name, fn entry ts, line entry ts, accumulated subcall time ( = 0)
	}

	
//
// @desc Captures execution statistics for the statement just completed.
//
// @param i {int}		Specifies the origin-0 index of the stack level.
// @param n {int}		Specifies the line number within the function, starting from 1
//				  		and incrementing monotonically for each closed line.  The
//				  		value is negative if the statement exits the function.
// @param r {any}		Contains the result of the statement executed.  This value is
//				  		returned as our result.
//
// @return {any}		The result is the argument `r` without modification.
//	
mon:{[i;n;r]
	t:.z.n;s:PFS i;
	$[n<0;[if[i;PFS[i-1;3]+:t-s 1];PFS::i#PFS];PFS[i;2 3]:1 0*t]; / Accrue subcall time to parent on return; else reset line and subcall times
	PFD[first s;1 2 3;-1+abs n]+:(1i;t-s 2;s 3); / Count, total time, subcall time
	r
	}

	
//
// @desc Transforms a function by introducing profiler execution logic before the
// first statement and after the execution of each closed line.  A line is considered
// closed if there is no active nesting of parentheses, brackets, or braces (other
// than the outer braces that define the scope of the function itself), and the line
// ends in a semicolon or is the last line of a function.
//
// @param nm {symbol}	Specifies the name of the function to transform.
// @param fn {string}	Specifies the definition of the function.
//
// @return {list}		A 3-element array containing the text of the transformed
//						function, a vector of line numbers, and a corresponding array
//						of line snippets (with snippet length controlled by the
//						global `LL`); or, an empty array if the function has already
//						been instrumented for profiling.
//
xf:{[nm;fn]
	fn:(k:2*"k)"~2#fn)_-1_fn; / Ignore trailing brace, and distinguish q vs. k
	fn[where fn="\t"]:" "; / Map tabs to blanks
	ln>:(|)(&\)(|)(fn=" ")|ln:fn="\n"; / Ignore trailing lines
	if[0h<type j:cmm[fn;0,where ln;q:qtm fn];fn@:j:where j;ln@:j;q@:j]; / Mark (with 0's) unescaped quote chars and remove comments
	p:q*(+\)1 -1 1 -1 1 -1i["()[]{}"?fn]*q:(=\)q; / Cumulative overall nesting level
	p*:1i=(+\)1 -1i["{}"?fn]*q; / Ignore nested lambdas
	j:where q<={x@:where j:i|-1_0b,i:x<>" ";i|expand[j;((("-"=1_x),0b)&-1_0b,x in")]}")|(1_k,0b)&-1_0b,k:x in CH]}fn;p@:j;fn@:j;ln@:j; / Remove redundant white space
	j:where(";"=(";",fn)i)&1i=p i:0,where ln; / Lines to consider, with leading NL	
	if[count ss[first[i[1_j],count fn]#fn]"p99:.prof.";:""]; / Skip if instrumented
	f:{[nm;n;v;p]
		s:_[o+:("\n"<>_[o:$[(t:1<abs n)<"{["~2#v;1+v?"]";1]]v)?1b]v;p:o _p; / Offset to code start and resultant string
		a:(a+1),rz[;s;p]each a:ra[s;p]; / Compute return starts and corresponding ends
		if[(c:not count s)<1<>a 0;a:0,a,count[s]-((|)s in"\n;")?0b]; / Wrap non-empty, non-return stmt
		j:where[2#(_)0.5*count b]b:iasc a; / Distinguish starts from ends, in sequence
		e:(,/)((0,a b)_s),'(({".prof.mon[p99;",string[x],";["}each n,(-)abs n),(,)"]]")[j+a>0],(,)"";
		((o#v),$[t;"";"p99:.prof.init[`",nm,"];"],(count[e]*c)_e;(LL&count s)#s)
		}[string nm]'[j*1 -1[j=last j+:1];i[j]_fn;i[j]_p];
	((k#"k)"),/(first each f),"}";j;last each f)
	}

qtm:{[fn] (fn="\"")<=-1_0b,@[fn="\\";1+fn ss "\\\\";:;0b]} / Unescaped quotes (may be in comments)
cmm:{[fn;ln;q] $[1b in c:(fn in" \n")&1_(fn="/"),0b;[j:(cm\). 0b,ln _/:(q;c);(,/)j[;1]];1b]} / Comments
cm:{[b;q;c] i:first[b]=\q;j:first where[i<c],n:count q;(i[j-1];(j#1b),(n-j)#0b)} / Line comment
ra:{[s;p] where(p>0i)&(-1_1b,s in "\n[{;")&(s=":")>1_(s in ":;/)]}"),0b}; / Return starts
rz:{[i;s;p] i+(((";"=i _s)&j=k)|(j<k:p i)&0i<>j:i _p)?1b}; / Return ends


\d .

\

Usage:

.prof.prof`name						/ Profiles the specified function, or all functions in the specified namespace
.prof.prof`name1`name2				/ Profiles the specified functions, or all functions in the specified namespaces
.prof.prof`							/ Profiles all functions in all namespaces
.prof.unprof`name					/ Unprofiles the specified function, or all functions in the specified namespace
.prof.unprof`						/ Unprofiles all functions for which profiling is enabled
.prof.report`name					/ Produces a report of profile information for the specified function
.prof.report`						/ Produces a report of profile information for all profiled functions
.prof.data`name						/ Returns the raw profile data for the specified function
.prof.data`							/ Returns the raw profile data for all profiled functions
.prof.reset[]						/ Resets profile statistics, discarding previous results

Globals:

.prof.NSX - List of namespaces to exclude; assign to change
.prof.LL  - Number of leading chars of source lines to include in reports; assign to change
.prof.PFD - Dictionary of name -> stmt, count, CPU arrays (in line no. order)
.prof.PFS - Execution stack (contains name, time at start of entry to level, interim line residual)
.prof.SV  - Dictionary of saved (unprofiled) definitions
