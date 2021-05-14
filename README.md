# qprof

q code profiler

Contains routines to profile line-level statement execution counts and CPU
consumption, distinguishing between execution time consumed within the
function and within called functions.  Functions to be profiled can be specified
explicitly or by referencing a parent namespace (in which case
all functions in all namespaces below it are examined).
	
Profiling temporarily modifies a function by adding
instrumentation logic to it.  A copy of the original function
is first saved, and is restored when profiling is removed.
Note that if a profiled function is modified, changes to it
are lost when profiling is removed.

For each profiled line, the following data is collected:

* function name
* line number
* line display
* line execution count
* total time consumed on the line (including subcalls), in nanoseconds
* time consumed on the line itself, in nanoseconds

The profiler defines a line to be the shortest sequence of one or more source code lines
having no active nesting of parentheses, brackets, or braces (other
than the outer braces that define the scope of the function itself). The line
must end in a semicolon or be the last line of a function.

Profiling is efficient and is suitable for instrumenting entire workspaces of a running application.

> Note that attribution of subcall time may not be correct in a profiled
function that signals an event to a higher level.

# Usage

| Name and Syntax | Description |
| --------------- | ----------- |
| `.prof.prof[names]` | Profiles the specified functions, or all functions in the specified namespaces. If the argument is \`, all functions in all non-system namespaces are profiled |
| `.prof.unprof[names]` | Unprofiles the specified functions, or all functions in the specified namespaces for which profiling is enabled. Collected usage information is discarded. If the argument is \`, all profiled functions in all non-system namespaces are unprofiled |
| `.prof.report[names]` | Produces a report of collected profile information for the specified functions, or all functions in the specified namespaces for which profiling is enabled. If the argument is \`, all profiled functions in all non-system namespaces are included in the report. Execution times are reported in milliseconds. Only lines executed are included. The report is ordered by decreasing own line execution time |
| `.prof.data[names]` | Returns the raw data representing the collected profile information for the specified functions, or all functions in the specified namespaces for which profiling is enabled. If the argument is \`, all profiled functions in all non-system namespaces are included in the result. Only lines executed are included. The result is ordered alphabetically by function name and then by line number |
| `.prof.reset[names]` | Resets the profile statistics for all profiled functions, discarding previous results. The state of profiled functions is unaltered |

The variable `.prof.LL` can be adjusted to change the maximum length of the source line included in the collected data, as reflected by `.prof.report` and `.prof.data`.

# Changes

* The profiler now shows the percentage of time consumed on each line relative to all lines.
* The profiler report is now ordered by decreasing own line execution time.

# Author

Leslie Goldsmith, First Derivatives
