window.inputs = {

    'bpmn.Activity': {
        content: {
            type: 'textarea',
            label: 'Content',
            group: 'general',
            index: 1
        },
        icon: {
            type: 'select',
            options: ['none','message','user'],
            label: 'Icon',
            group: 'general',
            index: 2
        },
        activityType: {
            type: 'select',
            options: ['task', 'transaction', 'event-sub-process', 'call-activity'],
            label: 'Type',
            group: 'general',
            index: 3
        },
        subProcess: {
            type: 'toggle',
            label: 'Sub-process',
            group: 'general',
            index: 4
        },
        attrs: {
            '.body/fill': {
                type: 'color',
                label: 'Body Color',
                group: 'appearance',
                index: 1
            },
            '.label/text': {
                type: 'text',
                label: 'Weight',
                group: 'general',
                index: 2
            },
        }
    },

    'standard.Goal': {
        attrs: {
            '.label/text': {
                type: 'text',
                label: 'Name',
                group: 'general',
                index: 1
            },
            '.label/weight': {
                type: 'text',
                label: 'Weight',
                group: 'general',
                index: 2
            },
            '.body/fill': {
                type: 'color',
                label: 'Body Color',
                group: 'appearance',
                index: 3
            }
        }
    },

    'bpmn.Event': {
        attrs: {
            '.label/text': {
                type: 'text',
                label: 'Name',
                group: 'general',
                index: 1
            },
            '.label/weight': {
                type: 'text',
                label: 'Weight',
                group: 'general',
                index: 3
            },
            '.body/fill': {
                type: 'color',
                label: 'Body Color',
                group: 'appearance',
                index: 4
            }
        },
        eventType: {
            type: 'select',
            options: [
                { value: 'none', content: 'none' },
                { value: 'PCC', content: 'PCC' },
                { value: 'NCC', content: 'NCC' },
                { value: 'PVC', content: 'PVC' },
                { value: 'NVC', content: 'NVC' },
            ],
            label: 'Relation type',
            group: 'general',
            index: 2
        },
       
    },


    'bpmn.Flow': {
        flowType: {
            type: 'select',
            options: ['default','PCC','NCC','PVC','NVG','EXC'],
            label: 'Type',
            group: 'general',
            index: 1
        },
        '.label/weight': {
            type: 'text',
            label: 'Weight',
            group: 'general',
            index: 2
        },
    }
};
