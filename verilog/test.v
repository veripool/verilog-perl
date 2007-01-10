// $Id$
// DESCRIPTION: Verilog-Perl: Example Verilog for testing package
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2000-2007 by Wilson Snyder.

// ENCRYPT_ME

module example (/*AUTOARG*/
   // Outputs
   z, 
   // Inputs
   a, b
   );

   // See http://veripool.com
   // for what AUTOARG and friends can do for you!

   /*Comment // test*/
   //
   
   input a;
   input b;

   output z;

   wire result = a|b;

   wire z = result;

endmodule
