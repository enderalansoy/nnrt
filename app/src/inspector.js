window.inputs = {

    // 'bpmn.Activity': {
    //     content: {
    //         type: 'textarea',
    //         label: 'Content',
    //         group: 'general',
    //         index: 1
    //     },
    //     icon: {
    //         type: 'select',
    //         options: ['none','message','user'],
    //         label: 'Icon',
    //         group: 'general',
    //         index: 2
    //     },
    //     activityType: {
    //         type: 'select',
    //         options: ['task', 'transaction', 'event-sub-process', 'call-activity'],
    //         label: 'Type',
    //         group: 'general',
    //         index: 3
    //     },
    //     subProcess: {
    //         type: 'toggle',
    //         label: 'Sub-process',
    //         group: 'general',
    //         index: 4
    //     },
    //     attrs: {
    //         '.body/fill': {
    //             type: 'color',
    //             label: 'Body Color',
    //             group: 'appearance',
    //             index: 1
    //         },
    //         '.label/text': {
    //             type: 'text',
    //             label: 'Weight',
    //             group: 'general',
    //             index: 2
    //         },
    //     }
    // },

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

        // eventType: {
        //     type: 'select',
        //     options: [
        //         { value: 'none', content: 'none' },
        //         { value: 'PCC', content: 'PCC' },
        //         { value: 'NCC', content: 'NCC' },
        //         { value: 'PVC', content: 'PVC' },
        //         { value: 'NVC', content: 'NVC' },
        //     ],
        //     label: 'Relation type',
        //     group: 'general',
        //     index: 2
        // },
       
    },


    'bpmn.Flow': {
        // flowType: {
        //     type: 'select',
        //     options: ['default','PCC','NCC','PVC','NVG','EXC'],
        //     label: 'Type',
        //     group: 'general',
        //     index: 1
        // },
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
