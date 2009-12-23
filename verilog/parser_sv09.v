// 1800-2009 mantis1769
module mantis1769 #(N=1);
   if (N < 1) $error("Bad N value %d", N);
endmodule
