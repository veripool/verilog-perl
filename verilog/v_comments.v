`define ThirtyTwo 32

module v_comments ( a,                // Pragma for a
		    b,                // pragma for b
		    c,
		    d, d1, d2, d3 );
   input a;                     // comment for a
   inout [10:0] b;
   output [0:10] c;             // comment for c
   output [ ((2*`ThirtyTwo) - 1) : 0 ] d;
   output [ `ThirtyTwo : 0 ] d1;
   output [ ( MATH - 1 ): 0 ] d2;
   output [ `ThirtyTwo - 1: 0 ] d3;

   reg           d;
   reg [11:0]    e;             // Comment for e

endmodule

// 'Third' below must attach to 'b' becase there's no ) or , after b.
module v_bug917  // modcmt
  (input wire  a, // a-First
   output wire m // m-Second
   ,
   output wire b // b-Third
   );
   // Third
endmodule

module v_bug917p
  (input wire  a, // a-First
   output wire b); // b-Secondparen
   // Third
endmodule
