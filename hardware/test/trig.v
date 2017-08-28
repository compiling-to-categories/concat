/***
* trig.v - Trigonometric functions in Verilog.
*
* Original author: David Banas <capn.freako@gmail.com>
* Original date:   August 28, 2017
*
* Copyright (c) 2017 David Banas; all rights reserved World wide.
***/

module trig;
  parameter real    pi = 3.1416;
  parameter integer n  = 2;       // Last index of 'sin_vals'.

real sin_vals[0:n];

// Sine.
function real sin;
  input real x;

  begin
    x = x % (2 * pi);
    if (x > pi)
      sin = -_sin(x - pi);
    else if (x > pi/2)
      sin = _sin(pi/2 - (x % pi/2));
    else
      sin = _sin(x);
    if ()
  end
endfunction

function real _sin;
  input real x;

  begin
    ir = n * x / (pi/4);
    ix = $rtoi(ir);
    if (ix == n)
      _sin = 1.0;
    else
      _sin = sin_vals[ix] + (sin_vals[ix+1] - sin_vals[ix]) * (ir - ix);
  end
endfunction

// Cosine.
function real cos;
  input real x;

  begin
    cos = sin(x + pi/2);
  end
endfunction

// Tangent.
function real tan;
  input real x;

  begin
    tan = sin(x) / cos(x);
  end
endfunction

initial begin
  sin_vals[0]  = 0.0;
  sin_vals[1]  = 0.7071;
  sin_vals[2]  = 1.0;
end

