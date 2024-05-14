window;import{jsxs as e,jsx as n,Fragment as t}from"react/jsx-runtime";import*as r from"react";import{RpcContext as i,useAsyncPersistent as o,mapRpcError as c,importWidgetModule as u,EditorContext as s}from"@leanprover/infoview";var a=function(){return a=Object.assign||function(e){for(var n,t=1,r=arguments.length;t<r;t++)for(var i in n=arguments[t])Object.prototype.hasOwnProperty.call(n,i)&&(e[i]=n[i]);return e},a.apply(this,arguments)};function l(e,n,t,r){return new(t||(t=Promise))((function(i,o){function c(e){try{s(r.next(e))}catch(e){o(e)}}function u(e){try{s(r.throw(e))}catch(e){o(e)}}function s(e){var n;e.done?i(e.value):(n=e.value,n instanceof t?n:new t((function(e){e(n)}))).then(c,u)}s((r=r.apply(e,n||[])).next())}))}function f(e,n){var t,r,i,o,c={label:0,sent:function(){if(1&i[0])throw i[1];return i[1]},trys:[],ops:[]};return o={next:u(0),throw:u(1),return:u(2)},"function"==typeof Symbol&&(o[Symbol.iterator]=function(){return this}),o;function u(u){return function(s){return function(u){if(t)throw new TypeError("Generator is already executing.");for(;o&&(o=0,u[0]&&(c=0)),c;)try{if(t=1,r&&(i=2&u[0]?r.return:u[0]?r.throw||((i=r.return)&&i.call(r),0):r.next)&&!(i=i.call(r,u[1])).done)return i;switch(r=0,i&&(u=[2&u[0],i.value]),u[0]){case 0:case 1:i=u;break;case 4:return c.label++,{value:u[1],done:!1};case 5:c.label++,r=u[1],u=[0];continue;case 7:u=c.ops.pop(),c.trys.pop();continue;default:if(!(i=c.trys,(i=i.length>0&&i[i.length-1])||6!==u[0]&&2!==u[0])){c=0;continue}if(3===u[0]&&(!i||u[1]>i[0]&&u[1]<i[3])){c.label=u[1];break}if(6===u[0]&&c.label<i[1]){c.label=i[1],i=u;break}if(i&&c.label<i[2]){c.label=i[2],c.ops.push(u);break}i[2]&&c.ops.pop(),c.trys.pop();continue}u=n.call(e,c)}catch(e){u=[6,e],r=0}finally{t=i=0}if(5&u[0])throw u[1];return{value:u[0]?u[1]:void 0,done:!0}}([u,s])}}}function d(i,o,c){return l(this,void 0,void 0,(function(){var s,p,h,v,m,w,g,b,y,E,x,C,P,k,j,S,N,U=this;return f(this,(function(L){switch(L.label){case 0:return"text"in c?[2,n(t,{children:c.text})]:[3,1];case 1:if(!("element"in c))return[3,3];for(s=c.element,p=s[0],h=s[1],k=s[2],v={},m=0,w=h;m<w.length;m++)g=w[m],b=g[0],y=g[1],v[b]=y;return[4,Promise.all(k.map((function(e){return l(U,void 0,void 0,(function(){return f(this,(function(n){switch(n.label){case 0:return[4,d(i,o,e)];case 1:return[2,n.sent()]}}))}))})))];case 2:return j=L.sent(),"hr"===p?[2,n("hr",{})]:0===j.length?[2,r.createElement(p,v)]:[2,r.createElement(p,v,j)];case 3:return"component"in c?(E=c.component,x=E[0],C=E[1],P=E[2],k=E[3],[4,Promise.all(k.map((function(e){return l(U,void 0,void 0,(function(){return f(this,(function(n){switch(n.label){case 0:return[4,d(i,o,e)];case 1:return[2,n.sent()]}}))}))})))]):[3,6];case 4:return j=L.sent(),S=a(a({},P),{pos:o}),[4,u(i,o,x)];case 5:if(N=L.sent(),!(C in N))throw new Error("Module '".concat(x,"' does not export '").concat(C,"'"));return 0===j.length?[2,r.createElement(N[C],S)]:[2,r.createElement(N[C],S,j)];case 6:return[2,e("span",{className:"red",children:["Unknown HTML variant: ",JSON.stringify(c)]})];case 7:return[2]}}))}))}function p(u){var s=u.pos,a=u.html,l=r.useContext(i),f=o((function(){return d(l,s,a)}),[l,s,a]);return"resolved"===f.state?f.value:"rejected"===f.state?e("span",{className:"red",children:["Error rendering HTML: ",c(f.error).message]}):n(t,{})}"function"==typeof SuppressedError&&SuppressedError;var h=r.createContext({answer:function(e){console.warn("Uncaptured answer: ".concat(e))},pos:{uri:"dummy",line:0,character:0}});function v(e){return n("div",{children:n("p",{children:"No questions..."})})}function m(e){var t=r.useContext(h);var i=r.useRef(null);return r.useEffect((function(){null!==i.current&&i.current.reset()}),[e.elems]),n("form",{onSubmit:function(e){e.preventDefault();var n=new FormData(e.currentTarget);t.answer(Object.fromEntries(n))},ref:i,children:e.elems.map((function(e){return n(p,{pos:t.pos,html:e})}))})}function w(e,n){if(!("element"in e))return e;var t=e.element,r=t[0],i=t[1],o=t[2];if("button"==r||"a"==r){var c=i.slice();return"a"==r&&c.push(["className","pointer dim"]),c.push(["onClick",n]),{element:[r,c,o]}}return{element:[r,i,o.map((function(e){return w(e,n)}))]}}function g(e){return n(p,{html:w(e.html,e.onClick),pos:e.pos})}function b(t){var i=r.useRef(null),o=r.useContext(h);return e("div",{children:[n(p,{pos:o.pos,html:t.question}),n("div",{style:{display:"grid",alignItems:"center",justifyItems:"center"},ref:i,children:t.options.map((function(e,t){return n("div",{className:"grid-item",children:n(g,{html:e,pos:o.pos,onClick:function(){return o.answer(t)}})})}))})]})}var y={level:0,editPos:{line:0,character:0},widget:n("p",{children:"Initializing..."})};function E(t){var o=r.useState(y),c=o[0],u=o[1],d=r.useContext(i),v=r.useContext(s),m=r.useRef({line:0,character:0}),w=r.useRef(null);function g(e,n){if(null!==w.current){if(e!==m.current||0!==n.length){var t=n.map((function(e){return e+"\n"})).join("").trimEnd();0===n.length?m.current=e:m.current={line:e.line+n.length,character:n[n.length-1].length-1},0!==e.character&&(t="\n"+t,m.current={line:m.current.line+1,character:n[n.length-1].length-1});var r={start:e,end:m.current};!function(e,n){l(this,void 0,void 0,(function(){return f(this,(function(t){switch(t.label){case 0:return[4,v.api.applyEdit({documentChanges:[e]})];case 1:return t.sent(),[4,v.revealPosition(n)];case 2:return t.sent(),[2]}}))}))}({textDocument:w.current.ident,edits:[{range:r,newText:t}]},a(a({},m.current),{uri:w.current.ident.uri}))}}else n.length>0&&(console.warn("Document editing not initialized, cannot insert:"),console.warn(n))}function b(e,r,i,o){var c=m.current;for(var s=n(h.Provider,{value:{answer:function(e){return l(this,void 0,void 0,(function(){var n,t,r,i;return f(this,(function(s){switch(s.label){case 0:console.log("Answer:"),console.log(e),n=o,t=[],s.label=1;case 1:return[4,d.call("processUserAnswer",[e,n])];case 2:if(r=s.sent(),i=r[0],n=r[1],e=null,"insertLine"in i)t.push(i.insertLine.line);else{if(!("initEdit"in i))return g(c,t),u(b(v,i.widget.level,i.widget.w,n)),[3,3];console.warn("initEdit is only available suring initialization")}return[3,1];case 3:return[2]}}))}))},pos:t.pos},children:n(p,{html:i,pos:t.pos})}),a=e;void 0!==a&&a.level>=r;)a=a.parent;var v={level:r,widget:s,editPos:c,parent:a,previous:e};return v}function E(){return l(this,void 0,void 0,(function(){var e,n,r,i;return f(this,(function(o){switch(o.label){case 0:return[4,d.call("initializeInteraction",t.code)];case 1:e=o.sent(),n=e[0],r=e[1],w.current=null,o.label=2;case 2:if("insertLine"in n)console.warn("Edits disabled before user action");else{if(!("initEdit"in n))return w.current&&(m.current=w.current.startPos),u(b(void 0,n.widget.level,n.widget.w,r)),[3,4];w.current=n.initEdit}return[4,d.call("processUserAnswer",[null,r])];case 3:return i=o.sent(),n=i[0],r=i[1],[3,2];case 4:return[2]}}))}))}r.useEffect((function(){E()}),[t.pos.line]);for(var x=[],C=c;void 0!==C;)x.push(C.widget),C=C.parent;return x.reverse(),e("div",{children:[n("button",{onClick:function(){console.log("Undo"),console.log(c),void 0!==c.previous&&(g(c.previous.editPos,[]),u(c.previous))},children:"Undo"}),n("hr",{}),x]})}export{v as EmptyWidget,m as FormWidget,b as SelectWidget,E as default};