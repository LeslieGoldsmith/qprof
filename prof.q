/
	Q code profiler
	Copyright (c) 2014-2015 Affinity Systems

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public License as
	published by the Free Software Foundation; either version 2 of
	the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

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

	Author:		Leslie Goldsmith, Affinity Systems
\


\d .prof

NSX:`q`Q`h`j`o`prof / Namespace exclusion list
LL:30 / Number of source chars to show

PFD:(0#`)!PFS::()
if[not type key`SV;SV:PFD]


///
/F/ Enables profiling for specified functions.
///
/P/ x:symbol[]	- Specifies the names of the functions to profile.  Namespaces
/P/				  are replaced by the names of the functions within them,
/P/				  recursively.  If the argument is unspecified or is the empty
/P/				  symbol, all functions in all non-system namespaces are profiled.
///
prof:{
	{f:$[type key x;value x;0];
		$[100h<>type f;-2 "Not a function: ",string x;
			count t:xf[x;last v:value f];[PFD[x]:(enl last[t]j?1+til i),(i:last j:t 1)#'"inn"$0;SV[x]:f;def[x;first v 3;first t]];
			-2 "Already profiled: ",string x];
		} each fns x;
	}


///
/F/ Disables profiling for specified functions, and discards collected usage
/F/ information.
///
/P/ x:symbol[]	- Specifies the names of the functions to unprofile.  Namespaces
/P/				  are replaced by the names of the functions within them,
/P/				  recursively.  If the argument is unspecified or is the empty
/P/				  symbol, profiling is disabled for all functions for which it
/P/				  is enabled.
///
unprof:{
	{$[100h<>type f:SV x;-2 "Not profiled: ",string x;
		[x set f;{.[`.prof;(,)x;_;y]}\:[`SV`PFD;x]]];
		} each $[mt x;key SV;fns x];
	}


///
/F/ Resets profile statistics, discarding previous results.  The state of
/F/ profiled functions is unaltered.
///
reset:{PFD[;1 2 3]*:0;PFS::()}


///
/F/ Returns the raw data representing the profile execution results.  For each
/F/ profiled line on which execution occurred, the data includes the following:
/F/
/F/		* function name
/F/		* closed line number
/F/		* leading statement characters
/F/		* line execution count
/F/		* total time consumed on the line (including subcalls)
/F/		* time consumed on the line itself
/F/
/F/ Lines not executed are not included in the report.
///
/P/ x:symbol[]	- Specifies the names of the functions for which execution
/P/				  information is to be computed.  If the argument is unspecified
/P/				  or is the empty symbol, data is returned for all profiled
/P/				  functions.
///
/R/ A table containing the execution report, ordered alphabetically by function
/R/ and then by line number.
///
data:{
	x:$[mt x;key PFD;not(&/)b:(x,:())in key PFD;[-2 "Not profiled:",(,/)" ",'string x where not b;x where b];x];
	a:x where n:count each w:flip each PFD x; / Function names
	t:(-\)each(w:raze w)[;2 3]; / Total and own ( = total - subcall)
	asc select from ([]Name:a;Line:(,/)til each n;Stmt:w[;0];Count:w[;1];Total:t[;0];Own:t[;1]) where Count<>0
	}


///
/F/ Computes a usage report summarizing the profile execution results.  For each
/F/ profiled line on which execution occurred, the data includes the following:
/F/
/F/		* function name
/F/		* closed line number
/F/		* leading statement characters
/F/		* line execution count
/F/		* total time consumed on the line (including subcalls), in MM:SS.sss
/F/		* time consumed on the line itself, in MM:SS.sss
/F/
/F/ Lines not executed are not included in the report.
///
/P/ x:symbol[]	- Specifies the names of the functions for which execution
/P/				  information is to be computed.  If the argument is unspecified
/P/				  or is the empty symbol, the report is computed for all
/P/				  profiled functions.
///
/R/ A table containing the execution report, ordered by decreasing total line
/R/ execution time.
///
report:{
	t:`$5_''-6_''string each value flip select Total,Own from w:data x;
	`Total xdesc update Total:first t,Own:last t from w
	}


//
// Internal definitions.
//


enl:enlist
ns:~[1#.q]1#
mt:{(x~`)|x~(::)}
fns:{$[mt x;ff(key`.),getn ` sv'`,'(key`)except NSX;getn x]}
ff:{x where 100h=type each value each x}
getn:{(,/)getns each x}
getns:{$[type key x;$[ns value x;ff(j where not i),getn(j:` sv'x,'k)where i:ns each x k:1_key x;x];x]}
expand:{[msk;a] @[msk;where msk;:;a]}

CH:"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-`.:"


///
/F/ Defines a function within its associated namespace.
///
/P/ nm:symbol	- Specifies the fully-qualified name of the function to define.
/P/	c:symbol	- Specifies the context in which to define the function.
/P/	f:string	- Specifies the definition of the function.
///
def:{[nm;c;f]
	d:system "d";system "d .",string c; / Set namespace
	nm set value f; / Define object (reification performed by <value> must be under proper ns)
	system "d ",string d; / Restore previous namespace
	}


///
/F/ Initializes statistics collection on function entry.
///
/P/ nm:symbol	- Specifies the name of the function.
///
/R/ Origin-0 index of the stack level of the new function call.
///
init:{[nm]
	-1+count PFS,:enl nm,1 1 0*.z.n / Name, fn entry ts, line entry ts, accumulated subcall time ( = 0)
	}

	
///
/F/ Captures execution statistics for the statement just completed.
///
/P/ i:int		- Specifies the origin-0 index of the stack level.
/P/ n:int		- Specifies the line number within the function, starting from 1
/P/				  and incrementing monotonically for each closed line.  The
/P/				  value is negative if the statement exits the function.
/P/ r:any		- Contains the result of the statement executed.  This value is
/P/				  returned as our result.
///
/R/ The result is the argument <r> without modification.
///	
mon:{[i;n;r]
	t:.z.n;s:PFS i;
	$[n<0;[if[i;PFS[i-1;3]+:t-s 1];PFS::i#PFS];PFS[i;2 3]:1 0*t]; / Accrue subcall time to parent on return; else reset line and subcall times
	PFD[first s;1 2 3;-1+abs n]+:(1i;t-s 2;s 3); / Count, total time, subcall time
	r
	}


///
/F/ Transforms a function by introducing profiler execution logic before the first
/F/ statement and after the execution of each closed line.  A line is considered
/F/ closed if there is no active nesting of parentheses, brackets, or braces
/F/ (other than the outer braces that define the scope of the function itself),
/F/ and the line ends in a semicolon or is the last line of a function.
///
/P/ nm:symbol	- Specifies the name of the function to transform.
/P/ fn:string	- Specifies the definition of the function.
///
/R/ A 3-element array containing the text of the transformed function, a vector
/R/ of line numbers, and a corresponding array of line snippets (with snippet
/R/ length controlled by the variable <LL>); or, an empty array if the function
/R/ has already been instrumented for profiling.
///
xf:{[nm;fn]
	fn:(k:2*"k)"~2#fn)_-1_fn; / Ignore trailing brace, and distinguish q vs. k
	ln>:(|)(&\)(|)(fn=" ")|ln:fn="\n"; / Ignore trailing lines
	p:q*(+\)1 -1 1 -1 1 -1i["()[]{}"?fn]*q:(=\)(fn="\"")<=-1_0b,@[fn="\\";1+fn ss "\\\\";:;0b]; / Cumulative overall nesting level
	j:where q<={j:i|-1_0b,i:not x in "\t ";i|expand[j;(1_k,0b)&-1_0b,k:(x where j) in CH]} fn; / Mark (with 0's) redundant white space
	p@:j;ln@:j;fn[where "\t"=fn@:j]:" "; / Convert to more canonical form
	j:where @[";"=fn i-1;0,count[i]-1;:;1b]&1i=p i:0,where ln; / Lines to consider, with leading NL
	if[count ss[first[i[1_j],count fn]#fn]"p99:.prof.";:""]; / Skip if instrumented
	f:{[nm;n;v;p]
		s:_[o+:("\n"<>_[o:$[(t:1<abs n)<"{["~2#v;1+v?"]";1]]v)?1b]v;p:o _p; / Offset to code start and resultant string
		ra:{[s;p] where(p>0i)&(-1_1b,s in "\n([{;")&(s=":")>1_(s in ":;)]}"),0b}; / Return starts
		rz:{[i;s;p] j+(";"<>s j)&p[i]=p j:i+(((i _s)in "]};")&p[i]>=i _p)?1b}; / Return ends
		a:(a+1),rz[;s;p] each a:ra[s;p]; / Compute return starts and corresponding ends
		if[(c:not count s)<1<>a 0;a:0,a,count[s]-((|)s in "\n;")?0b]; / Wrap non-empty, non-return stmt
		j:where[2#(_)0.5*count b]b:iasc a; / Distinguish starts from ends, in sequence
		e:(,/)((0,a b)_s),'(({".prof.mon[p99;",string[x],";["}each n,(-)abs n),(,)"]]")[j+a>0],(,)"";
		((o#v),$[t;"";"p99:.prof.init[`",nm,"];"],(count[e]*c)_e;(LL&count s)#s)
		}[string nm]'[j*1 -1[j=last j+:1];i[j]_fn;i[j]_p];
	((k#"k)"),(,/)(first each f),"}";j;last each f)
	}

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