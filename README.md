# PlanarDistantPathWidget
Small Tk widget to visualise distant path routing in planar graphs.

# Workflow
- Draw an outline of the graph on the canvas
- Randomly generate a selectable number of points inside of the outline, and triangulate the point set.
- Delete any unwanted vertices using right-click.
- Create Terminals by selecting Mark Red/Mark Black and clicking on vertices of the outer face.
- Click "Select Path Endpoints" to enter routing mode. Select two different terminals and a path between them will automatically computed along the outer face. Pressing "T" will toggle the currently routed pair, i.e. select the other path along the outer face.
- Adapt presentation of the elements using the UI sliders and the Colors-menu.
- Press "Export PDF" to obtain a vector graphic of the routing.
