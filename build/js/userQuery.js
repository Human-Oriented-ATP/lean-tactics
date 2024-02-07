window;import{jsxs as e,jsx as n,Fragment as t}from"react/jsx-runtime";import*as r from"react";import{RpcContext as o,useAsyncPersistent as a,mapRpcError as i,importWidgetModule as c,EditorContext as u}from"@leanprover/infoview";var s=function(){return s=Object.assign||function(e){for(var n,t=1,r=arguments.length;t<r;t++)for(var o in n=arguments[t])Object.prototype.hasOwnProperty.call(n,o)&&(e[o]=n[o]);return e},s.apply(this,arguments)};function l(e,n,t,r){return new(t||(t=Promise))((function(o,a){function i(e){try{u(r.next(e))}catch(e){a(e)}}function c(e){try{u(r.throw(e))}catch(e){a(e)}}function u(e){var n;e.done?o(e.value):(n=e.value,n instanceof t?n:new t((function(e){e(n)}))).then(i,c)}u((r=r.apply(e,n||[])).next())}))}function f(e,n){var t,r,o,a,i={label:0,sent:function(){if(1&o[0])throw o[1];return o[1]},trys:[],ops:[]};return a={next:c(0),throw:c(1),return:c(2)},"function"==typeof Symbol&&(a[Symbol.iterator]=function(){return this}),a;function c(c){return function(u){return function(c){if(t)throw new TypeError("Generator is already executing.");for(;a&&(a=0,c[0]&&(i=0)),i;)try{if(t=1,r&&(o=2&c[0]?r.return:c[0]?r.throw||((o=r.return)&&o.call(r),0):r.next)&&!(o=o.call(r,c[1])).done)return o;switch(r=0,o&&(c=[2&c[0],o.value]),c[0]){case 0:case 1:o=c;break;case 4:return i.label++,{value:c[1],done:!1};case 5:i.label++,r=c[1],c=[0];continue;case 7:c=i.ops.pop(),i.trys.pop();continue;default:if(!(o=i.trys,(o=o.length>0&&o[o.length-1])||6!==c[0]&&2!==c[0])){i=0;continue}if(3===c[0]&&(!o||c[1]>o[0]&&c[1]<o[3])){i.label=c[1];break}if(6===c[0]&&i.label<o[1]){i.label=o[1],o=c;break}if(o&&i.label<o[2]){i.label=o[2],i.ops.push(c);break}o[2]&&i.ops.pop(),i.trys.pop();continue}c=n.call(e,i)}catch(e){c=[6,e],r=0}finally{t=o=0}if(5&c[0])throw c[1];return{value:c[0]?c[1]:void 0,done:!0}}([c,u])}}}function h(o,a,i){return l(this,void 0,void 0,(function(){var u,p,d,v,m,g,w,b,y,x,E,C,k,S,D,T,j,N=this;return f(this,(function(O){switch(O.label){case 0:return"text"in i?[2,n(t,{children:i.text})]:[3,1];case 1:if(!("element"in i))return[3,3];for(u=i.element,p=u[0],d=u[1],S=u[2],v={},m=0,g=d;m<g.length;m++)w=g[m],b=w[0],y=w[1],v[b]=y;return[4,Promise.all(S.map((function(e){return l(N,void 0,void 0,(function(){return f(this,(function(n){switch(n.label){case 0:return[4,h(o,a,e)];case 1:return[2,n.sent()]}}))}))})))];case 2:return D=O.sent(),"hr"===p?[2,n("hr",{})]:0===D.length?[2,r.createElement(p,v)]:[2,r.createElement(p,v,D)];case 3:return"component"in i?(x=i.component,E=x[0],C=x[1],k=x[2],S=x[3],[4,Promise.all(S.map((function(e){return l(N,void 0,void 0,(function(){return f(this,(function(n){switch(n.label){case 0:return[4,h(o,a,e)];case 1:return[2,n.sent()]}}))}))})))]):[3,6];case 4:return D=O.sent(),T=s(s({},k),{pos:a}),[4,c(o,a,E)];case 5:if(j=O.sent(),!(C in j))throw new Error("Module '".concat(E,"' does not export '").concat(C,"'"));return 0===D.length?[2,r.createElement(j[C],T)]:[2,r.createElement(j[C],T,D)];case 6:return[2,e("span",s({className:"red"},{children:["Unknown HTML variant: ",JSON.stringify(i)]}))];case 7:return[2]}}))}))}function p(c){var u=c.pos,l=c.html,f=r.useContext(o),p=a((function(){return h(f,u,l)}),[f,u,l]);return"resolved"===p.state?p.value:"rejected"===p.state?e("span",s({className:"red"},{children:["Error rendering HTML: ",i(p.error).message]})):n(t,{})}"function"==typeof SuppressedError&&SuppressedError;var d=r.createContext({answer:function(e){console.warn("Uncaptured answer: ".concat(e))},pos:{uri:"dummy",line:0,character:0}});function v(e){return n("div",{children:n("p",{children:"No questions..."})})}function m(e){var t=r.useContext(d);var o=r.useRef(null);return r.useEffect((function(){null!==o.current&&o.current.reset()}),[e.elems]),n("form",s({onSubmit:function(e){e.preventDefault();var n=new FormData(e.currentTarget);t.answer(Object.fromEntries(n))},ref:o},{children:e.elems.map((function(e){return n(p,{pos:t.pos,html:e})}))}))}function g(e,n){if(!("element"in e))return e;var t=e.element,r=t[0],o=t[1],a=t[2];if("button"==r||"a"==r){var i=o.slice();return"a"==r&&i.push(["className","pointer dim"]),i.push(["onClick",n]),{element:[r,i,a]}}return{element:[r,o,a.map((function(e){return g(e,n)}))]}}function w(e){return n(p,{html:g(e.html,e.onClick),pos:e.pos})}function b(t){var o=r.useRef(null),a=r.useContext(d);return e("div",{children:[n(p,{pos:a.pos,html:t.question}),n("div",s({ref:o},{children:t.options.map((function(e,t){return n(w,{html:e,pos:a.pos,onClick:function(){return a.answer(t)}})}))}))]})}var y={text:""};function x(t){var a=r.useState([y,null]),i=a[0],c=a[1],h=r.useRef([]),v=i[0],m=i[1],g=r.useContext(o),w=r.useContext(u);function b(e){return l(this,void 0,void 0,(function(){var n,t,r;return f(this,(function(o){switch(o.label){case 0:return n=e[0],t=e[1],console.log("Question structure"),console.log(n),"editDocument"in n?(r=n.editDocument.edit,h.current.length>0&&h.current[h.current.length-1].edits.push(r),[4,w.api.applyEdit({documentChanges:[r]})]):[3,3];case 1:return o.sent(),[4,g.call("processUserAnswer",[null,t])];case 2:return e=o.sent(),[3,4];case 3:return c([n.widget.w,t]),[3,5];case 4:return[3,0];case 5:return[2]}}))}))}function x(e){var n=e.newText.split("\n"),t=e.range.start.line+(n.length-1),r=n[n.length-1].length;1==n.length&&(r+=e.range.start.character);var o="";o=e.range.start.line==e.range.end.line?" ".repeat(e.range.end.character-e.range.start.character):"\n".repeat(e.range.end.line-e.range.start.line)+" ".repeat(e.range.end.character);var a={range:{start:e.range.start,end:{line:t,character:r}},newText:o};return console.log(a),a}return r.useEffect((function(){!function(){l(this,void 0,void 0,(function(){var e;return f(this,(function(n){switch(n.label){case 0:return[4,g.call("initializeInteraction",t.code)];case 1:return e=n.sent(),h.current=[],b(e),[2]}}))}))}()}),[t.pos.line]),n("div",{}),e("div",{children:[n("button",s({onClick:function(){console.log(h);var e=h.current.pop();void 0!==e&&(c(e.state),function(e){l(this,void 0,void 0,(function(){var n,t,r;return f(this,(function(o){switch(o.label){case 0:n=e.length-1,o.label=1;case 1:return n>=0?(t=e[n],r={textDocument:t.textDocument,edits:t.edits.map(x)},[4,w.api.applyEdit({documentChanges:[r]})]):[3,4];case 2:o.sent(),o.label=3;case 3:return n--,[3,1];case 4:return[2]}}))}))}(e.edits))}},{children:"Undo"})),n("hr",{}),n(d.Provider,s({value:{answer:function(e){return l(this,void 0,void 0,(function(){var n;return f(this,(function(t){switch(t.label){case 0:return[4,g.call("processUserAnswer",[e,m])];case 1:return n=t.sent(),h.current.push({state:i,edits:[]}),b(n),[2]}}))}))},pos:t.pos}},{children:n(p,{pos:t.pos,html:v})}))]})}export{v as EmptyWidget,m as FormWidget,b as SelectWidget,x as default};