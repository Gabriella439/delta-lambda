# ΔΛ (Delta-Lambda)

## Introduction :
> This langauge is a test language for an implementation of the type system  ΔΛ (Delta-Lambda) described by [de Bruijn] for simplifying the semantics of his [Automath] project.
Eventually I will post the Coq/Idris/Agda/etc... proofs for the compliance of  the code to the inferential rules specified by [De Groote].

## Syntax :

Non-terminals are in *italics*.
The symbols **->** (production), **|** (union), and **[ ]** (one or more) belong to the notation. 
All other symbols are terminals.

###expression syntax
<TABLE ALIGN="center" CELLPADDING="4">
<TR><TD><I>Expression</I></TD>
  <TD><B>-&gt;</B></TD>
  <TD><CODE>type</CODE></TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD><CODE>Identifier</code></TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
    <CODE>(</CODE> <I>Expression</I> <I>Expression</I> <CODE>)</CODE>
  </TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
    <CODE>(</CODE><CODE>let</CODE><CODE>(</CODE>
      <B>[</B> <I>Top</I> <B>]</B>
    <CODE>)</CODE> <I>Expression</I> <CODE>)</CODE>
  </TD>
</TR>
<TR>
    <TD></TD>
    <TD><B>|</B></TD>
    <TD><CODE>(</CODE><CODE>qualified</CODE>
      <CODE>(</CODE> <B>[</B> <I>Identifier</I> <B>]</B> <CODE>)</CODE>
            <CODE>)</CODE></TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
    <CODE>(</CODE> <CODE>lambda</CODE>
    <CODE>(</CODE> <B>[</B> 
      <CODE>(</CODE><I>Identifier</I> <I>Expression</I><CODE>)</CODE>
         <B>]</B>
    <CODE>)</CODE> <I>Expression</I> <CODE>)</CODE>
  </TD>
</TR>
</TABLE>

###top level syntax
<TABLE ALIGN="center" CELLPADDING="4">
<TR><TD><I>Top</I></TD>
  <TD><B>-&gt;</B></TD>
  <TD>
    <CODE>(</CODE><CODE>namespace</CODE><CODE>(</CODE>
      <B>[</B> <I>Identifier</I> <B>]</B>
    <CODE>)</CODE> <I>Expression</I> <CODE>)</CODE>
  </TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
    <CODE>(</CODE> <CODE>declare</CODE>
    <I>Identifier</I>
    <CODE>(</CODE> <B>[</B> 
      <CODE>(</CODE><I>Identifier</I> <I>Expression</I><CODE>)</CODE>
         <B>]</B>
    <CODE>)</CODE> <I>Expression</I> <CODE>)</CODE>
  </TD>
</TR>
<TR>
  <TD></TD>
  <TD><B>|</B></TD>
  <TD>
    <CODE>(</CODE> <CODE>define</CODE>
    <I>Identifier</I>
    <CODE>(</CODE> <B>[</B> 
      <CODE>(</CODE><I>Identifier</I> <I>Expression</I><CODE>)</CODE>
         <B>]</B>
    <CODE>)</CODE> <I>Expression</I>  <I>Expression</I>
    <CODE>)</CODE>
  </TD>
</TR>
</TABLE>

## Semantics :

## References :
 * [Generalising Automath by Means of a Lambda-Typed Lambda Calculus][de Bruijn] Keuker, D.W., Lopez-Escobar, E.G.K. and Smith, C.H., eds., *Mathematal Logic and Theoretical Computer Science*, pp. 71-92, by courtesy of Marcel Dekker Inc., New York.

 * [Reveiwing the Classical and the de Bruijn Notation for lambda-calculus and Pure Type Systems][Kamareddine] *J. Logic Computat*., Vol 11 No. 3, pp. 363-394, Oxford University Press.

 * [Defining λ-Typed λ-Calculi by Axiomatizing the Typing Relation][de Groote] P. Enjalbert, A. Finkel, and K.W. Wagner eds., *Lecture Notes in Computer Science, Vol. 665*, Springer-Verlag (1993), pp. 712-723., 10th Annual Symposium on Theoretical Aspects of Computer Science, STACS’93.

[Automath]: http://www.win.tue.nl/automath/
[de Bruijn]: ../Documents/de_Bruijn.pdf
[de Groote]: ../Documents/de_Groote.pdf
[Kamareddine]: ../Documents/Kamareddine.pdf
