A Failed Experiment 
=============

This was supposed to become a tool wherein you could mark an expression
at a certain point as Do Not Erase, meaning that it would complain
if you overwrote that value.

Well turns out that in the face of recursive functions, this tool
wouldn't work, since the pointer analysis isn't powerful enough. Also,
It would have been impossible to filter out which stores happen before
and after the comment, mostly because concurrent functions. Rather
than being wrong, I'd rather be clever, so I've left the structure
for the parts that are valuable to share.

The main thing that this package contains though is a method for
doing synthetic queries with the pointer analysis package.

Roughly it works by finding the special comment, parsing the expression
within that comment, inserting an anonymous function call with the
expression as a parameter, typechecking the resulting program and
building the SSA form. The SSA form can then be used as a backing
for pointer analysis queries.

I hope this is useful. I suspect it is too hard to make into a library,
so copy away.
