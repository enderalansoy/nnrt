/*! Rappid v2.4.0 - HTML5 Diagramming Framework - TRIAL VERSION

Copyright (c) 2015 client IO

 2018-11-23 


This Source Code Form is subject to the terms of the Rappid Trial License
, v. 2.0. If a copy of the Rappid License was not distributed with this
file, You can obtain one at http://jointjs.com/license/rappid_v2.txt
 or from the Rappid archive as was distributed by client IO. See the LICENSE file.*/


window.inputs = {

    'bpmn.Gateway': {
        icon: {
            type: 'select',
            options: [
                { value: 'none', content: 'default' },
                { value: 'cross', content: 'exclusive' },
                { value: 'circle', content: 'inclusive' },
                { value: 'plus', content: 'parallel' }
            ],
            label: 'Type',
            group: 'general',
            index: 2
        },
        attrs: {
            '.label/text': {
                type: 'text',
                label: 'Name',
                group: 'general',
                index: 1
            },
            '.body/fill': {
                type: 'color',
                label: 'Body Color ',
                group: 'appearance',
                index: 1
            }
        }
    },

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
            }
        }
    },

    'bpmn.Event': {
        eventType: {
            type: 'select',
            options: ['start','end','intermediate'],
            group: 'general',
            label: 'Type',
            index: 2
        },
        icon: {
            type: 'select',
            options: [
                { value: 'none', content: 'none' },
                { value: 'cross', content: 'cancel' },
                { value: 'message', content: 'message' },
                { value: 'plus', content: 'parallel multiple' }
            ],
            label: 'Subtype',
            group: 'general',
            index: 3
        },
        attrs: {
            '.label/text': {
                type: 'text',
                label: 'Name',
                group: 'general',
                index: 1
            },
            '.body/fill': {
                type: 'color',
                label: 'Body Color',
                group: 'appearance',
                index: 1
            }
        }
    },


    'bpmn.Flow': {
        flowType: {
            type: 'select',
            options: ['default', 'conditional','normal','message','association','conversation'],
            label: 'Type',
            group: 'general',
            index: 1
        }
    }
};
