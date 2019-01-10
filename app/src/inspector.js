window.inputs = {

    'standard.Goal': {

        attrs: {
            'label/text': {
                type: 'text',
                label: 'Name',
                group: 'general',
                index: 1
            },
            'title': {
                type: 'textarea',
                label: 'Description',
                group: 'general',
                index: 2
            },
            '.label/mandatory': {
                type: 'select',
                label: 'Is Mandatory',
                options: ['no', 'yes'],
                group: 'general',
                index: 3
            },
            '.label/theme': {
                type: 'text',
                label: 'Theme',
                group: 'general',
                index: 4
            },
            '.label/weight': {
                type: 'list',
                label: 'Weights',
                group: 'Weights',
                item: {
                  type: 'object',
                  properties: {
                    attrs: {
                      text: {
                        title: {
                          type: 'text',
                          label: 'Weight Type',
                          index: 1
                        },
                        body: {
                          type: 'text',
                          label: 'Weight value',
                          index: 2,
                        }
                      },
                    } 
                  } 
                } 
              },
        }
    },

    'bpmn.Event': {
        attrs: {
            'label/text': {
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
            }
        },       
    },


    'bpmn.Flow': {
        attrs: {
            '.label/relation': {
                type: 'select',
                label: 'Relationship',
                options:[
                    { value: 'none', content: 'none' },
                    { value: 'PCC', content: 'PCC' },
                    { value: 'NCC', content: 'NCC' },
                    { value: 'PVC', content: 'PVC' },
                    { value: 'NVC', content: 'NVC' },
                    { value: 'EXC', content: 'EXC' },
                    { value: 'PRE', content: 'PRE' },
                ],
                index: 1,
            },
            '.label/weight': {
                type: 'text',
                label: 'Weight',
                group: 'general',
                index: 2
            },
        }
    }
};
