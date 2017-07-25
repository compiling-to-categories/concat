
function get_shader(gl,source,type) {
    var shader = gl.createShader(type);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
        alert("ERROR IN shader:\n" + gl.getShaderInfoLog(shader));
        return false;
    }
    return shader;
};

function install_effect(canvas,effect_frag_source) {
  // var effect = canvas.innerHTML;
  // console.dir("canvas effect == " + effect);
  var gl;
  try {
      gl = canvas.getContext("webgl", {antialias: true,alpha:false});
  } catch (e) {
      alert("You are not webgl compatible :(") ;
      return false;
  }
  // alert ("gl.SAMPLES == " + gl.getParameter(gl.SAMPLES));

  // Geometry
  var TRIANGLE_VERTEX =  gl.createBuffer ();
  gl.bindBuffer(gl.ARRAY_BUFFER, TRIANGLE_VERTEX);
  gl.bufferData(gl.ARRAY_BUFFER,new Float32Array([-1,-1, 1,-1, 1,1, -1,1]),
                gl.STATIC_DRAW);
  var TRIANGLE_FACES =  gl.createBuffer();
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, TRIANGLE_FACES);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER,new Uint16Array([0,1,2, 0,2,3]),
                gl.STATIC_DRAW);

  // I want to experiment with blending for cheap temporal and
  // spatial antialiasing.
  gl.disable(gl.DEPTH_TEST);
  gl.enable(gl.BLEND);
  gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
  /*
  gl.blendEquation( gl.FUNC_SUBTRACT );
  */
  gl.clearColor(1.0, 0.0, 0.0, 0.0);

  var panX,panY;
  var tweak_pan = function(moveX,moveY) { // in pixels
//       console.log("pan was (" + panX + "," + panY + ")" );
      panX += moveX * pixel_size;
      panY += moveY * pixel_size;
//       console.log("pan = (" + panX + "," + panY + ")" );
      gl.uniform2f(_pan,panX,panY);
      queue_draw();
  }

  var _position, _time, _zoom, _pan; // Attributes & uniforms
  var program = null;
  var choose_effect = function (frag) {
      // console.log("choose_effect: " + frag);
      // console.log("program == " + program);
      /* Try to clean up from previous effect. I don't know whether
         this step is necessary or sufficient. I still see the old
         programs in Firefox's Shader Editor.
      */
      if (program) gl.deleteProgram(program);
      program = gl.createProgram();
      gl.attachShader(program, get_shader(gl,vert_glsl,gl.VERTEX_SHADER));
      gl.attachShader(program, get_shader(gl,utils_glsl + frag, gl.FRAGMENT_SHADER));
      gl.linkProgram(program);
      // Attributes & uniforms
      _position = gl.getAttribLocation(program, "position");
      _time = gl.getUniformLocation(program, "in0"); // "time"
      if (!_time) console.log("non-animated");
      _zoom = gl.getUniformLocation(program, "zoom");
      _pan  = gl.getUniformLocation(program, "pan");
      gl.enableVertexAttribArray(_position);
      gl.useProgram(program);
      panX = 0; panY = 0;
      // Resize to set pan & zoom uniforms.
      canvas.onresize();
      tweak_pan(0,0);
  };

  var redraw = function(t) {
      if (_time) {
          gl.uniform1f(_time, t/1000);
          queue_draw();
      }
      // gl.clear(gl.COLOR_BUFFER_BIT);
      // gl.clear(0);
      gl.bindBuffer(gl.ARRAY_BUFFER, TRIANGLE_VERTEX);
      gl.vertexAttribPointer(_position, 2, gl.FLOAT, false,4*2,0) ;
      gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, TRIANGLE_FACES);
      gl.drawElements(gl.TRIANGLES, 6, gl.UNSIGNED_SHORT, 0);
      // gl.flush();
  };
  var queue_draw = function() { window.requestAnimationFrame(redraw); }
  var pixel_size; // in GL units

  canvas.onresize = function () {
      var w = canvas.width, h = canvas.height;
      var mi = Math.min(w,h), ma = Math.max(w,h);
      gl.viewport((w-ma)/2, (h-ma)/2, ma,ma);
      gl.uniform1f(_zoom, mi/ma);
      pixel_size = 2/ma;
      // console.log("zoom == " + mi/ma + "; pixel_size == " + pixel_size);
      queue_draw();
  }
  var dragging = false;
  var prevX, prevY;
  canvas.onmousedown = function (event) {
      dragging = true;
      prevX = event.clientX; prevY = event.clientY;
      // console.log("down"); 
  };
  canvas.onmouseup = function (event) { dragging = false; /* console.log("up"); */ };
  canvas.onmousemove = function (event) {
      if (dragging) {
          var x = event.clientX, y = event.clientY;
          var dx = x-prevX, dy= prevY-y;  // note y inversion
          // console.log("delta = (" + dx + "," + dy + ")" );
          tweak_pan(dx,dy);
          prevX=x; prevY=y;
      }
  };
  choose_effect(effect_frag_source);
};

var utils_glsl =
`
// Misc common definitions
precision mediump float;

// vec4 gray (float q) { return vec4(q,q,q,1.0); }
vec4 gray (float q) {
    const float alpha = 1.0;
    return vec4(alpha*q,alpha*q,alpha*q,alpha);
}
vec4 bw (bool b) { return gray(b?1.0:0.0); }

uniform float zoom;
uniform vec2 pan;
varying vec2 v_position;

bool effect (float in1, float in2);
vec4 effectV (vec2 p) { return bw(effect(p.x,p.y)); }

// void main () { gl_FragColor = effect(v_position / zoom - pan); }
void main () { gl_FragColor = effectV((v_position - pan) / zoom); }
`

// Simple vertex shader
var vert_glsl = `
attribute vec2 position;
varying vec2 v_position;

void main(void) {
    gl_Position = vec4(position, 0., 1.);
    v_position = position;
}
`

// Render a uniform variable from JSON to string
function uniformString(uniform) { return "uniform " + uniform.type + " " + uniform.name + ";\n"; }

// Render a shader object from JSON to string
function shaderString(uniforms,effect) {
    return uniforms.map(uniformString).join() + effect;
}

// Assumes a canvas element with id "effect_canvas" and a global variable named "effect"
function go() {
    var canvas = document.getElementById("effect_canvas");
    var effect_source = shaderString(uniforms,effect)
    // console.log("effect object:\n\n" + JSON.stringify(effect) );
    // console.log("effect source:\n\n" + effect_source );
    install_effect(canvas,effect_source);
    window.onresize = function() {
	canvas.width = window.innerWidth;
	canvas.height = window.innerHeight;
	canvas.onresize();
    };
    window.onresize();
}
