## To do

*   Try [side-by-side divs](https://www.google.com/search?q=html+side+by+side+divs) for widgets, and place min & max values and perhaps the name and value.
    See the commented-out section at the end of style.css.
*   Put examples on [GitHub pages](https://pages.github.com/).
    I'd have to somehow put script.js and the examples into a GitHub repo.
*   Colorful examples.
*   Start re-populating `ConCat.Graphics.Image`
*   Add some 3D as well from [Vertigo](http://conal.net/papers/Vertigo), shaders, etc from the Shady source code, improving things along the way.
    Use CCC-based automatic differentiation for computing normal vectors (for shading).
*   Revisit [tangible values](http://conal.net/papers/Eros/) (without gestural composition for now), changing to the standard CCC interfaces as another application of compiling-to-categories.
*   As part of the tangible-values-based GUIs, we'll probably want to generate some simple JavaScript code, which I think we can do easily in the style of `ConCat.Graphics.GLSL` and `ConCat.SMT` (in concat/examples).
    This part will be nifty and useful elsewhere as well, so probably move it into concat/examples or another repo at some point.
    We'll need to pick a JavaScript GUI library.
    I don't know much about them, but maybe you do.
*   For 3D in Shady and Vertigo, I used uniform triangle meshes.
    I'd love to use geometry shaders instead, as they seem much more in the spirit of continuous procedural graphics and maybe could be made adaptive to lighting, curvature, etc.
*   Performance improvement:
    *   Use vector/SIMD operations.
