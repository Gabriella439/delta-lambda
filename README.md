# ΔΛ (Delta-Lambda)

## Introduction :
This langauge is a test language for an implementation of the type system  ΔΛ (Delta-Lambda) described by [de Bruijn] for simplifying the semantics of his [Automath] project.
Eventually I will post the Coq/Idris/Agda/etc... proofs for the compliance of  the code to the inferential rules specified by [De Groote].

## Syntax :

Non-terminals are in *italics*.
The symbols **->** (production), **|** (union), and **[ ]** (one or more) belong to the notation. 
All other symbols are terminals.

### expression syntax
<TABLE ALIGN="center" CELLPADDING="4">
<TR><TD><I>Expression</I></TD>
  <TD><B>-&gt;</B></TD>
  <TD><CODE>type</CODE></TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>Identifier</TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
    <CODE>(</CODE> <I>Vector</I>  <CODE>)</CODE> <I>Expression</I>
  </TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
  <CODE>[</CODE> <I>Telescope</I> <CODE>]</CODE> <I>Expression</I>
  </TD>
</TR>
<TR>
  <TD><I>Vector</I></TD>
  <TD><B>-&gt;</B></TD>
  <TD><I>Expression</I></TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD><I>Expression</I> <CODE>,</CODE> <I>Vector</I></TD>
</TR>
<TR>
  <TD><I>Telescope</I></TD>
  <TD><B>-&gt;</B></TD>
  <TD> <I>Identifiers</I> <CODE>:</CODE> <I>Expression</I></TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD><I>Identifiers</I> <CODE>:</CODE> <I>Expression</I> <CODE>,</CODE> <I>Telescope</I></TD>
</TR>
<TR>
  <TD><I>Identifiers</I></TD>
  <TD><B>-&gt;</B></TD>
  <TD>Identifier</TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>Identifiers <I>Identifiers</I></TD>
</TR>
</TABLE>

## Semantics :
the sematics of delta-lambda are fairly simple, and involve inductive definitions on the structure of expressions. We will step through the inductive relations on terms and describe them in detail. We assume that beta equivalence is known to be the reflexive transitive symmetric closure of beta reduction, which is defined as normal. the notation <CODE>[x := A]B</CODE> is used to represent substitution, which also takes on the typical meaning (pedants may examine [de Bruijn]'s paper)

here are the relations (the names of which are the same in the code): 
 1. typeOf
   * the typeOf function produces the type of a term, by replacing the tail variable with it's type

> typeOf[context, x] = A if [x : A] in context

> typeOf[context, (A) B] = (A) typeOf[context, B]

> typeOf[context, [x : A] B] = [x: A] typeOf[[x : A] context, B])

 2. ftype
   * this function produces the 'final' type of a term, that is the term ends in <CODE>type</CODE>. (note that this essentially preforms eta expansion)


> ftype[context, A] = A if tail[A] is type

> ftype[context, A] = typef[context, typeOf[context, A]] if tail[A] is not type 


 4. tail
   * this function computes the term at the 'end' of a spine.

> tail[type] = type

> tail[x] = x

> tail[(A) B] = tail[B]

> tail[[x : A] B] = tail[B]

 5. correct
   * this is the most important structural function, it's purpose is to prove (or disprove) that a given term is (or is not) correct.

> correct[context, type] = true

> correct[context, x] = true iff (x A) in context, else false

> correct[context, [x : A] B] = correct[context, A] and correct[[x : A] context, B]

> correct[context, (A) B] = correct[B] and typing[context, A] is beta equivalent to some [x : C] D and typeOf[context, B] is beta equivalent to C and correct[context, [x := B]D]

It must be reiterated that proofs of the conformance of these structural relations on Expressions have not been written yet, as the relations are not simply recursive, so a proof in Coq/Agda/Idris/etc... will be very difficult
Also note that the code does not exatly follow this formalism.

## References :
 * [Generalising Automath by Means of a Lambda-Typed Lambda Calculus][de Bruijn] Keuker, D.W., Lopez-Escobar, E.G.K. and Smith, C.H., eds., *Mathematal Logic and Theoretical Computer Science*, pp. 71-92, by courtesy of Marcel Dekker Inc., New York.

 * [Reveiwing the Classical and the de Bruijn Notation for lambda-calculus and Pure Type Systems][Kamareddine] *J. Logic Computat*., Vol 11 No. 3, pp. 363-394, Oxford University Press.

 * [Defining λ-Typed λ-Calculi by Axiomatizing the Typing Relation][de Groote] P. Enjalbert, A. Finkel, and K.W. Wagner eds., *Lecture Notes in Computer Science, Vol. 665*, Springer-Verlag (1993), pp. 712-723., 10th Annual Symposium on Theoretical Aspects of Computer Science, STACS’93.

[Automath]: http://www.win.tue.nl/automath/
[de Bruijn]: Documents/de_Bruijn.pdf
[de Groote]: Documents/de_Groote.pdf
[Kamareddine]: Documents/Kamareddine.pdf
