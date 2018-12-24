
joint.setTheme('bpmn');

var example = window.example;
var gdAuth = window.gdAuth;
var gdLoad = window.gdLoad;
var gdSave = window.gdSave;
var inputs = window.inputs;
var toolbarConfig= window.toolbarConfig;

var graph = new joint.dia.Graph({ type: 'bpmn' });

var commandManager = new joint.dia.CommandManager({ graph: graph });

var keyboard = new joint.ui.Keyboard();

var jsonOfGraph = {};

let smtOutput = '';

var paper = new joint.dia.Paper({
    width: 2000,
    height: 2000,
    model: graph,
    gridSize: 10,
    defaultLink: new joint.shapes.bpmn.Flow,
    validateConnection: function(cellViewS, magnetS, cellViewT, magnetT, end) {

        // don't allow loop links
        if (cellViewS == cellViewT) return false;

        var view = (end === 'target' ? cellViewT : cellViewS);

        // don't allow link to link connection
        return !view.model.isLink();
    },
    embeddingMode: true,
    frontParentOnly: false,
    defaultAnchor: { name: 'perpendicular' },
    defaultConnectionPoint: { name: 'boundary', args: { sticky: true, stroke: true }},
    validateEmbedding: function(childView, parentView) {
        var Pool = joint.shapes.bpmn.Pool;
        return (parentView.model instanceof Pool) && !(childView.model instanceof Pool);
    }
}).on({

    'blank:pointerdown': function(evt, x, y) {

        if (keyboard.isActive('shift', evt)) {
            selection.startSelecting(evt, x, y);
        } else {
            selection.cancelSelection();
            paperScroller.startPanning(evt, x, y);
        }
    },

    'element:pointerdown': function(cellView, evt) {

        // Select an element if CTRL/Meta key is pressed while the element is clicked.
        if (keyboard.isActive('ctrl meta', evt) && !(cellView.model instanceof joint.shapes.bpmn.Pool)) {
            selection.collection.add(cellView.model);
        }
    },

    'element:pointerup': openTools,
    'link:options': openTools
});

var paperScroller = new joint.ui.PaperScroller({
    autoResizePaper: true,
    padding: 50,
    paper: paper
});

paperScroller.$el.appendTo('#paper-container');
paperScroller.center();

/* SELECTION */

var selection = new joint.ui.Selection({
    paper: paper,
    graph: graph,
    filter: ['bpmn.Pool'] // don't allow to select a pool
}).on({

    'selection-box:pointerdown': function(cellView, evt) {
        // Unselect an element if the CTRL/Meta key is pressed while a selected element is clicked.
        if (keyboard.isActive('ctrl meta', evt)) {
            selection.collection.remove(cellView.model);
        }
    }
});

/* STENCIL */

var stencil = new joint.ui.Stencil({
    graph: graph,
    paper: paper,
    dragEndClone: function(cell) {

        var clone = cell.clone();
        var type = clone.get('type');

        // some types of the elements need resizing after they are dropped
        var sizeMultiplier = { 'bpmn.Pool': 8 }[type];

        if (sizeMultiplier) {
            var originalSize = clone.get('size');
            clone.set('size', {
                width: originalSize.width * sizeMultiplier,
                height: originalSize.height * sizeMultiplier
            });
        }

        return clone;
    }
});

joint.dia.Element.define('bpmn.Event', {
    attrs: {
        body: {
            rx: 20,
            ry: 20,
            refWidth: '40%',
            refHeight: '40%',
            strokeWidth: 1,
            stroke: '#000000',
            fill: '#FFFFFF'
        },
        label: {
            textVerticalAnchor: 'middle',
            textAnchor: 'middle',
            refX: '50%',
            refY: '50%',
            fontSize: 14,
            fill: '#333333'
        },
        markup: [{
            tagName: 'rect',
            selector: 'body',
        }, {
            tagName: 'text',
            selector: 'label'
        }]
    }
}, {
    markup: [{
        tagName: 'rect',
        selector: 'body',
    }, {
        tagName: 'text',
        selector: 'label'
    }]
});


joint.dia.Element.define('standard.Goal', {
    attrs: {
        body: {
            rx: 20, // add a corner radius
            ry: 20,
            refWidth: '100%',
            refHeight: '100%',
            strokeWidth: 1,
            stroke: '#000000',
            fill: '#FFFFFF'
        },
        label: {
            textVerticalAnchor: 'middle',
            textAnchor: 'middle',
            refX: '50%',
            refY: '50%',
            fontSize: 14,
            fill: '#333333'
        },
        markup: [{
            tagName: 'rect',
            selector: 'body',
        }, {
            tagName: 'text',
            selector: 'label'
        }]
    }
}, {
    markup: [{
        tagName: 'rect',
        selector: 'body',
    }, {
        tagName: 'text',
        selector: 'label'
    }]
});

stencil.render().$el.appendTo('#stencil-container');

stencil.load([
    new joint.shapes.bpmn.Activity,
    new joint.shapes.bpmn.Event,
    new joint.shapes.standard.Goal,
]);

joint.layout.GridLayout.layout(stencil.getGraph(), {
    columns: 100,
    columnWidth: 110,
    rowHeight: 110,
    dy: 20,
    dx: 20,
    resizeToFit: true
});

stencil.getPaper().fitToContent(0, 0, 10);

// Create tooltips for all the shapes in stencil.
stencil.getGraph().get('cells').each(function(cell) {
    new joint.ui.Tooltip({
        target: '.joint-stencil [model-id="' + cell.id + '"]',
        content: cell.get('type').split('.')[1],
        bottom: '.joint-stencil',
        direction: 'bottom',
        padding: 0
    });
});

/* CELL ADDED: after the view of the model was added into the paper */
graph.on('add', function(cell, collection, opt) {

    if (!opt.stencil) return;

    // open inspector after a new element dropped from stencil
    var view = paper.findViewByModel(cell);
    if (view) openTools(view);
});

/* KEYBOARD */

keyboard.on('delete backspace', function() {

    graph.removeCells(selection.collection.toArray());
});

function openTools(cellView) {

    var cell = cellView.model;
    var type = cell.get('type');

    window.inspector = joint.ui.Inspector.create('#inspector-container', {
        cell: cell,
        inputs: inputs[type],
        groups: {
            general: { label: type, index: 1 },
            appearance: { index: 2 }
        }
    });

    if (!cell.isLink() && !selection.collection.contains(cell)) {

        selection.collection.reset([]);
        // Add the cell into the selection collection silently
        // so no selection box is rendered above the cellview.
        selection.collection.add(cell, { silent: true });

        new joint.ui.FreeTransform({
            cellView: cellView,
            allowOrthogonalResize: false,
            allowRotation: false
        }).render();

        var halo = new joint.ui.Halo({
            cellView: cellView,
            theme: 'default',
            boxContent: function(cellView) {
                return cellView.model.get('type');
            }
        });
        halo.render();
        halo.removeHandle('rotate');
        halo.removeHandle('resize');
    }
}

function showStatus(message, type) {

    $('.status').removeClass('info error success').addClass(type).html(message);
    $('#statusbar-container').dequeue().addClass('active').delay(3000).queue(function() {
        $(this).removeClass('active');
    });
}


/* TOOLBAR */

var toolbar = new joint.ui.Toolbar({
    tools: toolbarConfig.tools,
    references: {
        paperScroller: paperScroller,
        commandManager: commandManager
    }
});


function smtize() {
    let funs = [];
    let goals = [];
    let targets = [];
    let sources = [];
    let refinements = [];
    let nodes = [];
    let i = 1;
    let j = 1;
    jsonOfGraph.cells.forEach((cell) => {
        if (cell.type == 'standard.Goal') {
            funs.push(`G${i}`);
            goals.push({id: cell.id, name: `G${i}`});
            i++;
        } else if (cell.type == 'bpmn.Event') {
            funs.push(`R${j}`);
            refinements.push({id: cell.id, name: `R${j}`});
            j++;
        } else if (cell.type == 'bpmn.Flow') {
            goals.forEach((goal) => {
                if (cell.target.id === goal.id) {
                    targets.push(cell.target.id);
                }
            })
            refinements.forEach((ref) => {
                if (cell.source.id === ref.id) {
                    sources.push(cell.source.id);
                }
            })
            
            nodes.push({id: cell.id, from: cell.source.id, to: cell.target.id});
        }
    });
    funs = funs.sort();
    
    console.log(targets);
    console.log(sources);
    console.log(nodes)

    // Declaration of Goal, Assumption and Refinement Propostions

    smtOutput += `;%%%%\n;Declaration of Goal, Assumption and Refinement Propostions\n;%%%%\n`;

    funs.forEach((fun) => {
        smtOutput += `(declare fun ${fun}) \n`;
    });

    smtOutput += `\n\n`;

    // Close-world

    smtOutput += `;%%%%\n;Close-world\n;%%%%\n`;

    let closeWorldPairings = [];
    nodes.forEach((node) => {
        if (targets.includes(node.to) && sources.includes(node.from)) {
            let goalName;
            let refName;
            goals.forEach((goal) => {
                if (goal.id === node.to) {
                    goalName = goal.name;
                }
            })
            refinements.forEach((ref) => {
                if (ref.id === node.from) {
                    refName = ref.name;
                }
            })
            closeWorldPairings.push({ goal: goalName, refinement: refName });
        }
    });

    console.log({closeWorldPairings});


    for (i = 0; i < closeWorldPairings.length; i +=1 ) {
        if (i > 0) {
            if (closeWorldPairings[i].goal != closeWorldPairings[i-1].goal) {
                smtOutput += `)))\n(assert (=> ${closeWorldPairings[i].goal}(or ${closeWorldPairings[i].refinement} `;
            } else {
                smtOutput += ` ${closeWorldPairings[i].refinement} `;
            }
        } else {
            smtOutput += `\n(assert (=> ${closeWorldPairings[i].goal}(or ${closeWorldPairings[i].refinement}`;
        }
       
    }

    smtOutput += `)))\n`

    smtOutput += `\n\n`;

    // Refinement-Goal relationships
    
    smtOutput += `;%%%%\n;Refinement-Goal relationships\n;%%%%\n`;

    console.log(smtOutput);

}

var toolbarCommands = {
    toJSON: function() {

        var windowFeatures = 'menubar=no,location=no,resizable=yes,scrollbars=yes,status=no';
        var windowName = _.uniqueId('json_output');
        var jsonWindow = window.open('', windowName, windowFeatures);

        jsonWindow.document.write(JSON.stringify(graph.toJSON()));

        jsonOfGraph = graph.toJSON();

        console.log(jsonOfGraph);
        smtize();
    },

    loadGraph: function() {

        gdAuth(function() {

            showStatus('loading..', 'info');
            gdLoad(function(name, content) {
                try {
                    var json = JSON.parse(content);
                    graph.fromJSON(json);
                    document.getElementById('fileName').value = name.replace(/.json$/, '');
                    showStatus('loaded.', 'success');
                } catch (e) {
                    showStatus('failed.', 'error');
                }
            });

        }, true);
    },

    saveGraph: function() {

        gdAuth(function() {

            showStatus('saving..', 'info');
            var name = document.getElementById('fileName').value;
            gdSave(name, JSON.stringify(graph.toJSON()), function(file) {

                if (file) {
                    showStatus('saved.', 'success');
                } else {
                    showStatus('failed.', 'error');
                }
            });

        }, true);
    }
};

toolbar.on({
    'tojson:pointerclick': toolbarCommands.toJSON,
    'load:pointerclick': toolbarCommands.loadGraph,
    'save:pointerclick': toolbarCommands.saveGraph,
    'clear:pointerclick': _.bind(graph.clear, graph),
    'print:pointerclick': _.bind(paper.print, paper)
});

toolbar.render().$el.appendTo('#toolbar-container');

toolbar.$('[data-tooltip]').each(function() {

    new joint.ui.Tooltip({
        target: this,
        content: $(this).data('tooltip'),
        top: '.joint-toolbar',
        direction: 'top'
    });
});
