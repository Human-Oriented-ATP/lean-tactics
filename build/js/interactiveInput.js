window;import{jsx as r}from"react/jsx-runtime";import*as t from"react";import{RpcContext as n}from"@leanprover/infoview";var e=function(){return e=Object.assign||function(r){for(var t,n=1,e=arguments.length;n<e;n++)for(var o in t=arguments[n])Object.prototype.hasOwnProperty.call(t,o)&&(r[o]=t[o]);return r},e.apply(this,arguments)};function o(r,t,n,e){return new(n||(n=Promise))((function(o,a){function i(r){try{c(e.next(r))}catch(r){a(r)}}function u(r){try{c(e.throw(r))}catch(r){a(r)}}function c(r){var t;r.done?o(r.value):(t=r.value,t instanceof n?t:new n((function(r){r(t)}))).then(i,u)}c((e=e.apply(r,t||[])).next())}))}function a(r,t){var n,e,o,a,i={label:0,sent:function(){if(1&o[0])throw o[1];return o[1]},trys:[],ops:[]};return a={next:u(0),throw:u(1),return:u(2)},"function"==typeof Symbol&&(a[Symbol.iterator]=function(){return this}),a;function u(u){return function(c){return function(u){if(n)throw new TypeError("Generator is already executing.");for(;a&&(a=0,u[0]&&(i=0)),i;)try{if(n=1,e&&(o=2&u[0]?e.return:u[0]?e.throw||((o=e.return)&&o.call(e),0):e.next)&&!(o=o.call(e,u[1])).done)return o;switch(e=0,o&&(u=[2&u[0],o.value]),u[0]){case 0:case 1:o=u;break;case 4:return i.label++,{value:u[1],done:!1};case 5:i.label++,e=u[1],u=[0];continue;case 7:u=i.ops.pop(),i.trys.pop();continue;default:if(!(o=i.trys,(o=o.length>0&&o[o.length-1])||6!==u[0]&&2!==u[0])){i=0;continue}if(3===u[0]&&(!o||u[1]>o[0]&&u[1]<o[3])){i.label=u[1];break}if(6===u[0]&&i.label<o[1]){i.label=o[1],o=u;break}if(o&&i.label<o[2]){i.label=o[2],i.ops.push(u);break}o[2]&&i.ops.pop(),i.trys.pop();continue}u=t.call(r,i)}catch(r){u=[6,r],e=0}finally{n=o=0}if(5&u[0])throw u[1];return{value:u[0]?u[1]:void 0,done:!0}}([u,c])}}}function i(i){var u=t.useContext(n);return r("form",e({onSubmit:function(r){r.preventDefault(),function(r){o(this,void 0,void 0,(function(){var t;return a(this,(function(n){switch(n.label){case 0:return t=Object.fromEntries(r),[4,u.call("Form.rpc",t)];case 1:return n.sent(),[2]}}))}))}(new FormData(r.currentTarget))}},{children:i.children}))}"function"==typeof SuppressedError&&SuppressedError;export{i as default};