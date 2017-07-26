
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

var timerCallbacks = [];

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

  var _position, _zoom, _pan; // Attributes & uniforms
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
      if (timerCallbacks.length > 0) {
          timerCallbacks.forEach(function (cb) { cb(t/1000) });
	  // queue_draw(); // in cb
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
  return { gl:gl, program:program, queue_draw:queue_draw };
};

var utils_glsl =
`
// Misc common definitions
precision mediump float;

uniform float zoom;
uniform vec2 pan;
varying vec2 v_position;

vec4 effect (float in1, float in2);
vec4 effectV (vec2 p) { return effect(p.x,p.y); }

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
    return uniforms.map(uniformString).join("") + effect;
}

function mkSlider(props,onChange) {
   var width = props.max - props.min;
   // map [0,10000] to [min,max]
   function to_rval (ival) { return ival / 10000 * width + props.min; };
   // map [min,max] to [0,10000]
   function to_ival (rval) { return (rval - props.min) / width * 10000; };
   var div = $("<div><p class=sliderLabel>"+props.label+": <input type=text class=param></p><p></p></div>");
   var input = div.find("input");
   var slider = div.find("p").filter(":last");
   slider.slider({
      value: to_ival(props.value), min: 0, max: 10000,
      slide: function(event, ui) {
        var rval = to_rval(ui.value);
        input.val(rval);
        if (onChange) onChange(rval);
      }
   });
   input.val(props.value);
   onChange(props.value);
   return div;
};

function mkTime(props,onChange) {
    // console.log("mkTime");
    timerCallbacks.push(onChange);
    return $("<div>(time)</div>");
}

var widgetMakers = { "slider": mkSlider, "time": mkTime };

function go(uniforms,effect) {
    var canvas = document.getElementById("effect_canvas");
    var effect_source = shaderString(uniforms,effect)
    // console.log("effect object:\n\n" + JSON.stringify(effect) );
    // console.log("effect source:\n\n" + effect_source );
    effect_info = install_effect(canvas,effect_source); // gl, program
    var gl  = effect_info.gl,
	program = effect_info.program,
	queue_draw = effect_info.queue_draw;
    uniforms.forEach(function (uniform) {
	var widget = uniform.widget,
	    loc = gl.getUniformLocation(program, uniform.name),
	    setVal = function (val) { gl.uniform1f(loc,val); queue_draw(); },
	    mk = widgetMakers[widget.type];
	$("div#ui").append(mk(widget, setVal));
    });
    window.onresize = function() {
	canvas.width  = window.innerWidth;
	canvas.height = window.innerHeight;
	canvas.onresize();
    };
    window.onresize();
}
